//#include "cvc4_public.h"

#include<iostream>
#include<vector>
#include<numeric>
#include<set>
#include<map>
#include "expr/node.h"
#include "expr/QuantifierEliminate.h"
#include "expr/attribute.h"
#include "printer/smt2/smt2_printer.h"
#include "util/output.h"
#include "theory/rewriter.h"
#include "theory/arith/normal_form.h"
#include "util/rational.h"
#include "util/integer.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/arith/arith_utilities.h"

//#include "theory/quantifiers/quantifiers_rewriter.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::expr;
using namespace CVC4::kind;
using namespace CVC4::printer;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;
using namespace CVC4::smt;

std::vector<std::vector<Node> > QuantifierEliminate::boundVar;
std::vector<Node> QuantifierEliminate::args;
std::vector<Container> QuantifierEliminate::container;
Integer QuantifierEliminate::lcmValue;
bool QuantifierEliminate::negationDone;
Integer QuantifierEliminate::negateCount;

bool QuantifierEliminate::isLiteralQE(Node n) {
  switch(n.getKind()) {
  case kind::NOT:
    return isLiteralQE(n[0]);
    break;
  case kind::OR:
  case kind::AND:
  case kind::IMPLIES:
  case kind::XOR:
  case kind::ITE:
  case kind::IFF:
    return false;
    break;
  default:
    break;
  }
  return true;
}
bool QuantifierEliminate::isRelationalOperatorTypeQE(Kind k) {
  switch(k) {
  case kind::LT:
  case kind::GT:
  case kind::LEQ:
  case kind::GEQ:
  case kind::EQUAL:
    return true;
  default:
    return false;
  }
}
bool QuantifierEliminate::isConstQE(Node n) {
  if(n.isConst())
    return true;
  else
    return false;
}
bool QuantifierEliminate::isVarQE(Node n) {
  if(n.isVar() && !isVarWithCoefficientsQE(n) && !isEquationQE(n))
    return true;
  else
    return false;
}
bool QuantifierEliminate::isVarWithCoefficientsQE(Node n) {
  if(n.getKind() == kind::MULT && isConstQE(n[0]) && isVarQE(n[1])) {
    return true;
  } else {
    return false;
  }
}

bool QuantifierEliminate::isEquationQE(Node n) {
  if((isRelationalOperatorTypeQE(n.getKind())) || (n.getKind() == kind::PLUS)
      || (n.getKind() == kind::MINUS))
    return true;
  else
    return false;
}

Node QuantifierEliminate::getCoefficientsOfExpression(Node n, Node bv) {
  Node coeff;
  if(n.hasBoundVar() && containsSameBoundVar(n, bv) && isVarQE(n)) {
    coeff = fromIntegerToNodeQE(1);
  } else if(n.hasBoundVar() && containsSameBoundVar(n, bv)
      && isVarWithCoefficientsQE(n)) {
    coeff = n[0];
  } else {
    for(Node::iterator i = n.begin(), iEnd = n.end(); i != iEnd; ++i) {
      Node c1 = *i;
      if(c1.hasBoundVar() && containsSameBoundVar(c1, bv)) {
        if(isVarQE(c1)) {
          coeff = fromIntegerToNodeQE(1);
        } else if(isVarWithCoefficientsQE(c1)) {
          coeff = c1[0];
        } else {
          coeff = getCoefficientsOfExpression(c1, bv);
        }

      } else {
      }
    }
  }
  Debug("expr-qetest")<<"coefficient "<<coeff<<std::endl;
  return coeff;
}
Node QuantifierEliminate::eliminateImpliesQE(Node body) {
  if(isLiteralQE(body)) {
    return body;
  } else {
    bool childrenChanged = false;
    std::vector<Node> children;
    for(unsigned i = 0; i < body.getNumChildren(); i++) {
      Node c = eliminateImpliesQE(body[i]);
      if(i == 0 && (body.getKind() == kind::IMPLIES)) {
        c = c.negate();
      }
      children.push_back(c);
      childrenChanged = childrenChanged || c != body[i];
    }
    if(body.getKind() == kind::IMPLIES) {
      return NodeManager::currentNM()->mkNode(OR, children);
    } else if(childrenChanged) {
      return NodeManager::currentNM()->mkNode(body.getKind(), children);
    } else {
      return body;
    }
  }
}

Node QuantifierEliminate::convertToNNFQE(Node body) {

  if(body.getKind() == kind::NOT) {
    if(body[0].getKind() == kind::NOT) {
      return convertToNNFQE(body[0][0]);
    } else if(isLiteralQE(body[0])) {
      return body;
    } else {
      std::vector<CVC4::Node> children;
      Kind k = body[0].getKind();
      if(body[0].getKind() == kind::OR || body[0].getKind() == kind::AND) {
        for(int i = 0; i < (int) body[0].getNumChildren(); i++) {
          children.push_back(convertToNNFQE(body[0][i].notNode()));
        }
        k = body[0].getKind() == kind::AND ? kind::OR : kind::AND;
      } else if(body[0].getKind() == kind::IFF) {
        for(int i = 0; i < 2; i++) {
          Node nn = i == 0 ? body[0][i] : body[0][i].notNode();
          children.push_back(convertToNNFQE(nn));
        }
      } else if(body[0].getKind() == kind::ITE) {
        for(int i = 0; i < 3; i++) {
          Node nn = i == 0 ? body[0][i] : body[0][i].notNode();
          children.push_back(convertToNNFQE(nn));
        }
      } else {
        Notice() << "Unhandled Quantifiers NNF: " << body << std::endl;
        return body;
      }
      return NodeManager::currentNM()->mkNode(k, children);
    }
  } else if(isLiteralQE(body)) {
    return body;
  } else {
    std::vector<CVC4::Node> children;
    bool childrenChanged = false;
    for(int i = 0; i < (int) body.getNumChildren(); i++) {
      Node nc = convertToNNFQE(body[i]);
      children.push_back(nc);
      childrenChanged = childrenChanged || nc != body[i];
    }
    if(childrenChanged) {
      return NodeManager::currentNM()->mkNode(body.getKind(), children);
    } else {
      return body;
    }
  }
}

Integer QuantifierEliminate::getIntegerFromNode(Node n) {
  Constant c = Constant::mkConstant(n);
  Rational r = c.getValue();
  Integer i = r.getNumerator();
  return i;
}
Node QuantifierEliminate::fromIntegerToNodeQE(Integer n) {
  Rational r(n);
  Constant c = Constant::mkConstant(r);
  return c.getNode();
}

Node QuantifierEliminate::getShiftedExpression(Node n, Node bv) {
  std::vector<Node> shiftedNodes;
  Node shift;
  for(Node::iterator l = n.begin(), l_end = n.end(); l != l_end; ++l) {
    Node childL = *l;
    if(childL.hasBoundVar() && containsSameBoundVar(childL, bv)) {
    } else {
      if(isVarQE(childL)) {
        Node convertChildL = NodeManager::currentNM()->mkNode(
            kind::MULT, fromIntegerToNodeQE(-1), childL);
        shiftedNodes.push_back(convertChildL);
      } else if(isVarWithCoefficientsQE(childL)) {
        Integer neg = getIntegerFromNode(childL[0]) * -1;
        TNode tn1 = childL[0];
        TNode tn2 = fromIntegerToNodeQE(neg);
        childL = childL.substitute(tn1, tn2);
        shiftedNodes.push_back(childL);
      } else {
        Integer neg = getIntegerFromNode(childL) * -1;
        Node convertChildL = fromIntegerToNodeQE(neg);
        shiftedNodes.push_back(convertChildL);
      }
    }
  }
  if(shiftedNodes.size() > 1) {
    shift = NodeManager::currentNM()->mkNode(kind::PLUS, shiftedNodes);
    return shift;
  } else {
    shift = shiftedNodes.back();
    shiftedNodes.pop_back();
    return shift;
  }
}
Node QuantifierEliminate::separateBoundVarExpression(Node n, Node bv) {
  Node toReturn;
  for(Node::iterator inner = n.begin(), inner_end = n.end(); inner != inner_end;
      ++inner) {
    Node innerChild = *inner;
    if(isConstQE(innerChild)) {
    } else {
      if(innerChild.hasBoundVar() && containsSameBoundVar(innerChild, bv)) {
        toReturn = innerChild;
        break;
      } else {
      }
    }

  }
  return toReturn;
}

void QuantifierEliminate::parseCoefficientQE(Node n, QuantifierEliminate q) {
  Node temp;
  if(n.getKind() == kind::NOT) {
    temp = n[0];
  } else {
    temp = n;
  }
  if(isConstQE(temp)) {
    Integer n = getIntegerFromNode(temp);
    Container c(temp, n);
    container.push_back(c);
  } else if(isVarQE(temp)) {
    Constant one = Constant::mkOne();
    Integer n = getIntegerFromNode(one.getNode());
    Container c(temp, n);
    container.push_back(c);
  } else if(isVarWithCoefficientsQE(temp)) {
    Integer n = getIntegerFromNode(temp[0]);
    Container c(temp[1], n);
    container.push_back(c);
  } else {
    for(Node::iterator i = temp.begin(), end = temp.end(); i != end; ++i) {
      Node child = *i;
      if(isVarWithCoefficientsQE(child)) {
        Integer n = getIntegerFromNode(child[0]);
        Container c(child[1], n);
        container.push_back(c);
      } else if(isConstQE(child)) {
        Integer n = getIntegerFromNode(child);
        Container c(child, n);
        container.push_back(c);
      } else if(isVarQE(child)) {
        Constant one = Constant::mkOne();
        Integer n = getIntegerFromNode(one.getNode());
        Container c(child, n);
        container.push_back(c);
      } else {
        parseCoefficientQE(child, q);
      }

    }
  }
}
Integer QuantifierEliminate::lcmQE(Integer a, Integer b) {
  return a.lcm(b);
}
Integer QuantifierEliminate::calculateLCMofCoeff(std::vector<Integer> coeffs) {
  Integer one = 1;
  Integer lcmResult = std::accumulate(coeffs.begin(), coeffs.end(), one, lcmQE);
  return lcmResult;
}
bool QuantifierEliminate::containsSameBoundVar(Node n, Node bv) {
  if(isVarQE(n)) {
    if(n == bv) {
      return true;
    } else {
      return false;
    }
  } else if(isVarWithCoefficientsQE(n)) {
    if(n[1] == bv) {
      return true;
    } else {
      return false;
    }
  } else {
    for(Node::iterator i = n.begin(), end = n.end(); i != end; ++i) {
      Node child = *i;
      if(isConstQE(child)) {
      } else if(isVarWithCoefficientsQE(child)) {
        if(child[1] == bv) {
          return true;
        } else {
        }
      } else if(isVarQE(child)) {
        if(child == bv) {
          return true;
        } else {
        }
      } else {
        for(Node::iterator i_inner = child.begin(), i_end = child.end();
            i_inner != i_end; ++i_inner) {
          Node child_inner = *i_inner;
          if(isVarQE(child_inner)) {
            if(child_inner == bv) {
              return true;
            } else {
            }
          } else if(isVarWithCoefficientsQE(child_inner)) {
            if(child_inner[1] == bv) {
              return true;
            } else {
            }
          } else {
          }
        }
      }
    }
    return false;
  }

}
Integer QuantifierEliminate::getLcmResult(Node t, Node bv,
                                          QuantifierEliminate q) {
  std::vector<Integer> boundVarCoeff;
  for(Node::kinded_iterator i = t.begin(t.getKind()), i_end = t.end(
      t.getKind()); i != i_end; ++i) {
    Node child = *i;
    Debug("expr-qetest")<<"In get Lcm Result child "<<child<<std::endl;
    parseCoefficientQE(child, q);
  }
  std::vector<Container> tempContainer = container;
  for(int i = 0; i < (int) tempContainer.size(); i++) {
    Debug("expr-qetest")<<"Variable "<<tempContainer[i].getVariable()<<" Coefficient "<<tempContainer[i].getCoefficient()<<std::endl;
  }
  Integer coeff = 1;
  for(int i = 0; i < (int) tempContainer.size(); i++) {
    if(tempContainer[i].getVariable() == bv) {
      boundVarCoeff.push_back(tempContainer[i].getCoefficient());
    }
  }
  Integer lcmResult = calculateLCMofCoeff(boundVarCoeff);
  Debug("expr-qetest")<<"lcmResult in getLcmResult "<<lcmResult<<std::endl;
  return lcmResult;
}

Node QuantifierEliminate::multiplyIndividualExpression(Node n, Node bv,
                                                       Integer multiple,
                                                       std::vector<Node> expr) {
  Debug("expr-qetest")<<"Expression before multiplication "<<n<<std::endl;
  for(Node::iterator it = n.begin(),it_end = n.end();
  it != it_end;
  ++it)
  {
    Node child = *it;
    Debug("expr-qetest")<<"child inside multiply individual expression "<<child<<std::endl;
    if(isConstQE(child))
    {
      child = fromIntegerToNodeQE(getIntegerFromNode(child)*multiple);
      Debug("expr-qetest")<<"temp node inside multiply individual expression "<<child<<std::endl;
      expr.push_back(child);
    }
    else if(isVarQE(child))
    {
      child = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(multiple),child);
      Debug("expr-qetest")<<"temp node inside multiply individual expression "<<child<<std::endl;
      expr.push_back(child);
    }
    else if(isVarWithCoefficientsQE(child))
    {
      child = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(multiple*getIntegerFromNode(child[0])),child[1]);
      Debug("expr-qetest")<<"temp node inside multiply individual expression "<<child<<std::endl;
      expr.push_back(child);
    }
    else
    {
      std::vector<Node> exprInner;
      Node test;
      test = multiplyIndividualExpression(child,bv,multiple,exprInner);
      expr.push_back(test);
    }
  }
  Node toReturn = NodeManager::currentNM()->mkNode(n.getKind(),expr);
  Debug("expr-qetest")<<"Expression after multiplication "<<toReturn<<std::endl;
  return toReturn;
}

Node QuantifierEliminate::multiplyEquationWithLcm(Node n, Node bv) {
  Node toReturn;
  std::vector<Node> multipliedExpression;
  Debug("expr-qetest")<<"Node n "<<n<<std::endl;
  Debug("expr-qetest")<<"bound var "<<bv<<std::endl;
  if(n.getKind() == kind::AND || n.getKind() == kind::OR) {
    for(Node::iterator i = n.begin(), iEnd = n.end(); i != iEnd; ++i) {
      Node c = *i;
      Debug("expr-qetest")<<"Node c "<<c<<std::endl;
      if(c.getKind() == kind::AND || c.getKind() == kind::OR) {
        toReturn = multiplyEquationWithLcm(c, bv);
      } else {
        Node t;
        if(c.getKind() == kind::NOT) {
          t = c[0];
        } else {
          t = c;
        }
        Integer coeff = 0;
        if(t[0].hasBoundVar() && containsSameBoundVar(t[0], bv)) {
          coeff = getIntegerFromNode(getCoefficientsOfExpression(t[0], bv));
          coeff = coeff.abs();
          Integer multiple = lcmValue.euclidianDivideQuotient(coeff);
          Debug("expr-qetest")<<"multiple "<<multiple<<std::endl;
          if(multiple == 1) {
            toReturn = c;
          } else {
            std::vector < Node > multipliedExpression;
            toReturn = multiplyIndividualExpression(t, bv, multiple,
                                                    multipliedExpression);
            if(c.getKind() == kind::NOT) {
              toReturn = toReturn.negate();
            }
            Debug("expr-qetest")<<"Node toReturn in multiply expression "<<toReturn<<std::endl;
          }
        }
        else if(t[1].hasBoundVar() && containsSameBoundVar(t[1],bv))
        {
          coeff = getIntegerFromNode(getCoefficientsOfExpression(t[1],bv));
          coeff = coeff.abs();
          Integer multiple = lcmValue.euclidianDivideQuotient(coeff);
          Debug("expr-qetest")<<"multiple "<<multiple<<std::endl;
          if(multiple == 1)
          {
            toReturn = c;
          }
          else
          {
            std::vector<Node> multipliedExpression;
            toReturn = multiplyIndividualExpression(t,bv,multiple,multipliedExpression);
            if(c.getKind() == kind::NOT)
            {
              toReturn = toReturn.negate();
            }
            Debug("expr-qetest")<<"Node toReturn in multiply expression "<<toReturn<<std::endl;
          }
        }
        else
        {
          toReturn = c;
        }
      }
      multipliedExpression.push_back(toReturn);
    }
    Node returnNode = NodeManager::currentNM()->mkNode(n.getKind(),
                                                       multipliedExpression);
    Debug("expr-qetest")<<"returnNode in multiply expression "<<returnNode<<std::endl;
    return returnNode;
  } else {
    Node t;
    Node toReturn;
    if(n.getKind() == kind::NOT) {
      t = n[0];
    } else {
      t = n;
    }
    Integer coeff = 0;
    if(t[0].hasBoundVar() && containsSameBoundVar(t[0], bv)) {
      coeff = getIntegerFromNode(getCoefficientsOfExpression(t[0], bv));
      coeff = coeff.abs();
      Integer multiple = lcmValue.euclidianDivideQuotient(coeff);
      Debug("expr-qetest")<<"multiple "<<multiple<<std::endl;
      if(multiple == 1) {
        toReturn = n;
      } else {
        std::vector < Node > multipliedExpression;
        toReturn = multiplyIndividualExpression(t, bv, multiple,
                                                multipliedExpression);
        if(n.getKind() == kind::NOT) {
          toReturn = toReturn.negate();
        }
        Debug("expr-qetest")<<"Node toReturn in multiply expression "<<toReturn<<std::endl;
      }
    }
    else if(t[1].hasBoundVar() && containsSameBoundVar(t[1], bv))
    {
      coeff = getIntegerFromNode(getCoefficientsOfExpression(t[1], bv));
      coeff = coeff.abs();
      Integer multiple = lcmValue.euclidianDivideQuotient(coeff);
      if(multiple == 1) {
        toReturn = n;
      } else {
        std::vector<Node> multipliedExpression;
        toReturn = multiplyIndividualExpression(t,bv,multiple,multipliedExpression);
        if(n.getKind() == kind::NOT)
        {
          toReturn = toReturn.negate();
        }
        Debug("expr-qetest")<<"Node toReturn in multiply expression "<<toReturn<<std::endl;
      }
    }
    else
    {
      toReturn = n;
    }
    Debug("expr-qetest")<<"returnNode in multiply expression "<<toReturn<<std::endl;
    return toReturn;
  }
}
Node QuantifierEliminate::parseEquation(Node t, Node bv,
                                        QuantifierEliminate q) {
  //std::vector<ExpressionContainer> temExpContainer = q.getExpContainer(q);
  Integer coeff = 1;
  Node n;
  if(t.getKind() == kind::NOT) {
    n = t[0];
  } else {
    n = t;
  }
  Integer lcmResult = getLcmResult(n, bv, q);
  lcmValue = lcmResult;
  Debug("expr-qetest")<<"lcm "<<lcmResult<<std::endl;
  Debug("expr-qetest")<<"container size "<<container.size()<<std::endl;
  std::vector<Container> tempContainer = container;
  for(int i = 0; i < (int) tempContainer.size(); i++) {
    if(tempContainer[i].getVariable() == bv) {
      coeff = tempContainer[i].getCoefficient();
    }
  }
  Debug("expr-qetest")<<"Coeff "<<coeff<<std::endl;
  Integer multiple = lcmResult.euclidianDivideQuotient(coeff.abs());
  Debug("expr-qetest")<<"multiple "<<multiple<<std::endl;
  while(!container.empty()) {
    container.pop_back();
  }
  if(lcmResult == 1 || multiple == 1) {
    Debug("expr-qetest")<<"After lcm operation expression "<<t<<std::endl;
    return t;
  }
  else
  {
    Node returnNode = multiplyEquationWithLcm(t,bv);
    Debug("expr-qetest")<<"After multiplication operation expression before replace of lcm*x with x "<<returnNode<<std::endl;
    Node replace1 = NodeManager::currentNM()->mkNode(kind::MULT, fromIntegerToNodeQE(lcmValue),bv);
    Node replace2 = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(lcmValue*(-1)),bv);
    TNode tn1 = replace1;
    TNode tn2 = replace2;
    TNode tn3 = bv;
    Node replace3 = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(-1),bv);
    TNode tn4 = replace3;
    returnNode = returnNode.substitute(tn1,tn3);
    returnNode = returnNode.substitute(tn2,tn4);
    Debug("expr-qetest")<<"After multiplication operation expression after replace of lcm*x with x "<<returnNode<<std::endl;
    return returnNode;
  }
}
Node QuantifierEliminate::replaceGTQE(Node n, Node bv) {
  Node returnNode;
  if(n.hasBoundVar() && containsSameBoundVar(n, bv)) {
    Node left = n[0];
    Node right = n[1];
    if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
      if(isVarQE(left) || isVarWithCoefficientsQE(left)) {
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, right, left);
        return returnNode;
      } else {
        Node shiftedNodes = getShiftedExpression(left, bv);
        left = separateBoundVarExpression(left, bv);
        if(!shiftedNodes.isNull()) {
          right = NodeManager::currentNM()->mkNode(kind::PLUS, right,
                                                   shiftedNodes);
        }
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, right, left);
        return returnNode;
      }
    } else {
      if(isVarQE(right) || isVarWithCoefficientsQE(right)) {
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, right, left);
        return returnNode;
      } else {
        Node shiftedNodes = getShiftedExpression(right, bv);
        right = separateBoundVarExpression(right, bv);
        if(!shiftedNodes.isNull()) {
          left = NodeManager::currentNM()->mkNode(kind::PLUS, left,
                                                  shiftedNodes);
        }
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, right, left);
        return returnNode;
      }
    }
  } else {
    Node left = n[0];
    Node right = n[1];
    returnNode = NodeManager::currentNM()->mkNode(kind::LT, right, left);
    return returnNode;
  }
}
Node QuantifierEliminate::replaceGEQQE(Node n, Node bv) {
  Node returnNode;
  if(n.hasBoundVar() && containsSameBoundVar(n, bv)) {
    Node left = n[0];
    Node right = n[1];
    Node tempLeft;
    Node tempRight;
    if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
      tempLeft = left;
      tempRight = right;
      if(tempLeft.getKind() == kind::PLUS
          || tempLeft.getKind() == kind::MINUS) {
        Node shiftedFromLeft = getShiftedExpression(tempLeft, bv);
        tempLeft = separateBoundVarExpression(tempLeft, bv);
        if(tempRight.getKind() == kind::PLUS
            || tempRight.getKind() == kind::MINUS) {

          bool flag = false;
          for(Node::iterator rightBegin = tempRight.begin(), rightEnd =
              tempRight.end(); rightBegin != rightEnd; ++rightBegin) {
            Node childR = *rightBegin;
            if(isConstQE(childR)) {
              Integer x = getIntegerFromNode(childR);
              x = x - 1;
              TNode tn1 = childR;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempRight = tempRight.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, shiftedFromLeft,
                  fromIntegerToNodeQE(-1));
            } else {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
            }
          } else {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(kind::PLUS,
                                                           tempRight,
                                                           shiftedFromLeft);
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        } else {
          if(isConstQE(tempRight)) {
            Integer x = getIntegerFromNode(tempRight);
            x = x - 1;
            tempRight = fromIntegerToNodeQE(x);
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(kind::PLUS,
                                                           tempRight,
                                                           shiftedFromLeft);
            }
          } else {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, shiftedFromLeft,
                  fromIntegerToNodeQE(-1));
            } else {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        }
      } else {
        if(tempRight.getKind() == kind::PLUS
            || tempRight.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator rightBegin = tempRight.begin(), rightEnd =
              tempRight.end(); rightBegin != rightEnd; ++rightBegin) {
            Node childR = *rightBegin;
            if(isConstQE(childR)) {
              Integer x = getIntegerFromNode(childR);
              x = x - 1;
              TNode tn1 = childR;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempRight = tempRight.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        } else {
          if(isConstQE(tempRight)) {
            Integer x = getIntegerFromNode(tempRight);
            x = x - 1;
            tempRight = fromIntegerToNodeQE(x);
          } else {

            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        }
      }
    } else {
      tempLeft = left;
      tempRight = right;
      if(tempRight.getKind() == kind::PLUS
          || tempRight.getKind() == kind::MINUS) {
        Node shiftedFromRight = getShiftedExpression(tempRight, bv);
        tempRight = separateBoundVarExpression(tempRight, bv);
        if(tempLeft.getKind() == kind::PLUS
            || tempLeft.getKind() == kind::MINUS) {

          bool flag = false;
          for(Node::iterator leftBegin = tempLeft.begin(), leftEnd =
              tempLeft.end(); leftBegin != leftEnd; ++leftBegin) {
            Node childL = *leftBegin;
            if(isConstQE(childL)) {
              Integer x = getIntegerFromNode(childL);
              x = x + 1;
              TNode tn1 = childL;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempLeft = tempLeft.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, shiftedFromRight,
                  fromIntegerToNodeQE(1));
            } else {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, fromIntegerToNodeQE(1));
            }
          } else {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                          shiftedFromRight);
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        } else {
          if(isConstQE(tempLeft)) {
            Integer x = getIntegerFromNode(tempLeft);
            x = x + 1;
            tempRight = fromIntegerToNodeQE(x);
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                          shiftedFromRight);
            }
          } else {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, shiftedFromRight,
                  fromIntegerToNodeQE(1));
            } else {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, fromIntegerToNodeQE(1));
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        }

      } else {
        if(tempLeft.getKind() == kind::PLUS
            || tempLeft.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator leftBegin = tempLeft.begin(), leftEnd =
              tempLeft.end(); leftBegin != leftEnd; ++leftBegin) {
            Node childL = *leftBegin;
            if(isConstQE(childL)) {
              Integer x = getIntegerFromNode(childL);
              x = x + 1;
              TNode tn1 = childL;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempLeft = tempLeft.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        } else {
          if(isConstQE(tempLeft)) {
            Integer x = getIntegerFromNode(tempLeft);
            x = x - 1;
            tempRight = fromIntegerToNodeQE(x);
          } else {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(1));
          }

          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        }
      }
    }
    return returnNode;
  } else {
    Node left = n[0];
    Node right = n[1];
    if(isConstQE(right)) {
      Integer x = getIntegerFromNode(right);
      x = x - 1;
      right = fromIntegerToNodeQE(x);
    } else {
      right = NodeManager::currentNM()->mkNode(kind::PLUS, right,
                                               fromIntegerToNodeQE(-1));
      right = Rewriter::rewrite(right);
    }
    returnNode = NodeManager::currentNM()->mkNode(kind::LT, right, left);
    return returnNode;
  }
}
Node QuantifierEliminate::replaceLEQQE(Node n, Node bv) {
  Node returnNode;
  if(n.hasBoundVar() && containsSameBoundVar(n, bv)) {
    Node left = n[0];
    Node right = n[1];
    Node tempLeft;
    Node tempRight;
    if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
      tempLeft = left;
      tempRight = right;
      if(tempLeft.getKind() == kind::PLUS
          || tempLeft.getKind() == kind::MINUS) {
        Node shiftedFromLeft = getShiftedExpression(tempLeft, bv);
        tempLeft = separateBoundVarExpression(tempLeft, bv);
        if(tempRight.getKind() == kind::PLUS
            || tempRight.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator rightBegin = tempRight.begin(), rightEnd =
              tempRight.end(); rightBegin != rightEnd; ++rightBegin) {
            Node childR = *rightBegin;
            if(isConstQE(childR)) {
              Integer x = getIntegerFromNode(childR);
              x = x + 1;
              TNode tn1 = childR;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempRight = tempRight.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, shiftedFromLeft,
                  fromIntegerToNodeQE(1));
            } else {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, fromIntegerToNodeQE(1));
            }
          } else {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(kind::PLUS,
                                                           tempRight,
                                                           shiftedFromLeft);
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempRight)) {
            Integer x = getIntegerFromNode(tempRight);
            x = x + 1;
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, shiftedFromLeft, fromIntegerToNodeQE(x));
            } else {
              tempRight = fromIntegerToNodeQE(x);
            }

          } else {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, shiftedFromLeft,
                  fromIntegerToNodeQE(1));
            } else {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, fromIntegerToNodeQE(1));
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        }

      } else {
        tempLeft = left;
        tempRight = right;
        if(tempRight.getKind() == kind::PLUS
            || tempRight.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator rightBegin = tempRight.begin(), rightEnd =
              tempRight.end(); rightBegin != rightEnd; ++rightBegin) {
            Node childR = *rightBegin;
            if(isConstQE(childR)) {
              Integer x = getIntegerFromNode(childR);
              x = x + 1;
              TNode tn1 = childR;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempRight = tempRight.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempRight)) {
            Integer x = getIntegerFromNode(tempRight);
            x = x + 1;
            tempRight = fromIntegerToNodeQE(x);
          }

          else {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        }
      }
    } else {
      tempLeft = left;
      tempRight = right;
      if(tempRight.getKind() == kind::PLUS
          || tempRight.getKind() == kind::MINUS) {
        Node shiftedFromRight = getShiftedExpression(tempRight, bv);
        tempRight = separateBoundVarExpression(tempRight, bv);
        if(tempLeft.getKind() == kind::PLUS
            || tempLeft.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator leftBegin = tempLeft.begin(), leftEnd =
              tempLeft.end(); leftBegin != leftEnd; ++leftBegin) {
            Node childL = *leftBegin;
            if(isConstQE(childL)) {
              Integer x = getIntegerFromNode(childL);
              x = x - 1;
              TNode tn1 = childL;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempLeft = tempLeft.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, shiftedFromRight,
                  fromIntegerToNodeQE(-1));
            } else {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
            }
          } else {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                          shiftedFromRight);
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempLeft)) {
            Integer x = getIntegerFromNode(tempLeft);
            x = x - 1;
            tempLeft = fromIntegerToNodeQE(x);
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                          shiftedFromRight);
            }
          } else {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, shiftedFromRight,
                  fromIntegerToNodeQE(-1));
            } else {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
            }
          }
        }
      } else {
        tempLeft = left;
        tempRight = right;
        if(tempLeft.getKind() == kind::PLUS
            || tempLeft.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator leftBegin = tempLeft.begin(), leftEnd =
              tempLeft.end(); leftBegin != leftEnd; ++leftBegin) {
            Node childL = *leftBegin;
            if(isConstQE(childL)) {
              Integer x = getIntegerFromNode(childL);
              x = x - 1;
              TNode tn1 = childL;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempLeft = tempLeft.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            tempLeft = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempLeft)) {
            Integer x = getIntegerFromNode(tempLeft);
            x = x - 1;
            tempLeft = fromIntegerToNodeQE(x);
          }

          else {
            tempLeft = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        }
      }
    }
  } else {
    Node left = n[0];
    Node right = n[1];
    if(isConstQE(right)) {
      Integer x = getIntegerFromNode(right);
      x = x + 1;
      right = fromIntegerToNodeQE(x);
    } else {
      right = NodeManager::currentNM()->mkNode(kind::PLUS, right,
                                               fromIntegerToNodeQE(1));
      right = Rewriter::rewrite(right);
    }
    returnNode = NodeManager::currentNM()->mkNode(kind::LT, left, right);
  }
  return returnNode;
}
Node QuantifierEliminate::replaceEQUALQE(Node n, Node bv) {
  if(n.hasBoundVar() && containsSameBoundVar(n, bv)) {
    Node left = n[0];
    Node right = n[1];
    Node finalLeft;
    Node finalRight;
    if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
      if(right.getKind() == kind::PLUS || right.getKind() == kind::MINUS) {
        Node tempLeft = left;
        Node tempRight = right;
        bool flag = false;
        Node shiftFromLeft;
        if(isVarQE(left) || isVarWithCoefficientsQE(left)) {
          tempLeft = left;
        } else {
          shiftFromLeft = getShiftedExpression(tempLeft, bv);
          tempLeft = separateBoundVarExpression(tempLeft, bv);
        }
        for(Node::iterator j = tempRight.begin(), j_end = tempRight.end();
            j != j_end; ++j) {
          Node child = *j;
          if(isConstQE(child)) {
            Integer x = getIntegerFromNode(child);
            x = x + 1;
            Node change = fromIntegerToNodeQE(x);
            TNode tn1 = child;
            TNode tn2 = change;
            tempRight = tempRight.substitute(tn1, tn2);
            flag = true;
            break;
          } else {
          }
        }
        if(!flag) {
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                         fromIntegerToNodeQE(1),
                                                         shiftFromLeft);
          } else {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(1));
          }

        } else {
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                         shiftFromLeft);
          }
        }
        finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                     tempRight);
        tempRight = right;
        bool flag1 = false;
        for(Node::iterator j = tempRight.begin(), j_end = tempRight.end();
            j != j_end; ++j) {
          Node child = *j;
          if(isConstQE(child)) {
            Integer x = getIntegerFromNode(child);
            x = x - 1;
            Node change = fromIntegerToNodeQE(x);
            TNode tn1 = child;
            TNode tn2 = change;
            tempRight = tempRight.substitute(tn1, tn2);
            flag1 = true;
            break;
          } else {
          }
        }
        if(!flag1) {
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1), shiftFromLeft);
          } else {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
          }

        } else {
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                         shiftFromLeft);
          }
        }

        finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                      tempLeft);
        Node returnNode = NodeManager::currentNM()->mkNode(kind::AND, finalLeft,
                                                           finalRight);
        return returnNode;
      } else {
        Node tempLeft = left;
        Node tempRight = right;
        Node shiftFromLeft;
        if(isVarQE(left) || isVarWithCoefficientsQE(left)) {
          tempLeft = left;
        } else {
          shiftFromLeft = getShiftedExpression(tempLeft, bv);
          tempLeft = separateBoundVarExpression(tempLeft, bv);
        }
        if(isConstQE(tempRight)) {
          Integer x = getIntegerFromNode(tempRight);
          x = x + 1;
          TNode tn1 = tempRight;
          TNode tn2 = fromIntegerToNodeQE(x);
          tempRight = tempRight.substitute(tn1, tn2);
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                         shiftFromLeft);
          }
        } else {
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                         fromIntegerToNodeQE(1),
                                                         shiftFromLeft);
          } else {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(1));
          }
        }
        finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                     tempRight);
        tempRight = right;
        if(isConstQE(right)) {
          Integer x = getIntegerFromNode(tempRight);
          x = x - 1;
          TNode tn1 = tempRight;
          TNode tn2 = fromIntegerToNodeQE(x);
          tempRight = tempRight.substitute(tn1, tn2);
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                         shiftFromLeft);
          }
        } else {
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1), shiftFromLeft);
          } else {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
          }

        }
        finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                      tempLeft);
        Node returnNode = NodeManager::currentNM()->mkNode(kind::AND, finalLeft,
                                                           finalRight);
        return returnNode;
      }
    } else {
      if(right.getKind() == kind::PLUS || right.getKind() == kind::MINUS) {
        Node tempLeft = left;
        Node tempRight = right;
        bool flag = false;
        Node shiftFromRight;
        if(isVarQE(right) || isVarWithCoefficientsQE(right)) {
          tempRight = right;
        } else {
          shiftFromRight = getShiftedExpression(tempRight, bv);
          tempRight = separateBoundVarExpression(tempRight, bv);
        }
        for(Node::iterator j = tempLeft.begin(), j_end = tempLeft.end();
            j != j_end; ++j) {
          Node childJ = *j;
          if(isConstQE(childJ)) {
            Integer x = getIntegerFromNode(childJ);
            x = x - 1;
            Node change = fromIntegerToNodeQE(x);
            TNode tn1 = childJ;
            TNode tn2 = change;
            tempLeft = tempLeft.substitute(tn1, tn2);
            flag = true;
            break;
          } else {
          }
        }
        if(!flag) {
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(-1),
                                                        shiftFromRight);
          } else {
            tempLeft = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
          }
        } else {
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        shiftFromRight);
          }
        }
        finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                     tempRight);
        tempLeft = left;
        bool flag1 = false;
        for(Node::iterator j = tempLeft.begin(), j_end = tempLeft.end();
            j != j_end; ++j) {
          Node child = *j;
          if(isConstQE(child)) {
            Integer x = getIntegerFromNode(child);
            x = x + 1;
            Node change = fromIntegerToNodeQE(x);
            TNode tn1 = child;
            TNode tn2 = change;
            tempLeft = tempLeft.substitute(tn1, tn2);
            flag1 = true;
            break;
          } else {
          }
        }
        if(!flag1) {
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(1),
                                                        shiftFromRight);
          } else {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(1));
          }
        } else {
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        shiftFromRight);
          }
        }
        finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                      tempLeft);
        Node returnNode = NodeManager::currentNM()->mkNode(kind::AND, finalLeft,
                                                           finalRight);
        return returnNode;
      } else {
        Node tempLeft = left;
        Node tempRight = right;
        Node shiftFromRight;
        if(isVarQE(right) || isVarWithCoefficientsQE(right)) {
          tempRight = right;
        } else {
          shiftFromRight = getShiftedExpression(tempRight, bv);
          tempRight = separateBoundVarExpression(tempRight, bv);
        }
        if(isConstQE(tempLeft)) {
          Integer x = getIntegerFromNode(tempLeft);
          x = x - 1;
          Node change = fromIntegerToNodeQE(x);
          TNode tn1 = tempLeft;
          TNode tn2 = change;
          tempLeft = tempLeft.substitute(tn1, tn2);
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        shiftFromRight);
          }
        } else {
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(-1),
                                                        shiftFromRight);
          } else {
            tempLeft = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
          }
        }
        finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                     tempRight);
        tempLeft = left;
        if(isConstQE(tempLeft)) {
          Integer x = getIntegerFromNode(tempLeft);
          x = x + 1;
          Node change = fromIntegerToNodeQE(x);
          TNode tn1 = tempLeft;
          TNode tn2 = change;
          tempLeft = tempLeft.substitute(tn1, tn2);
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        shiftFromRight);
          }
        } else {
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(1),
                                                        shiftFromRight);
          } else {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(1));
          }
        }
        finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                      tempLeft);
        Node returnNode = NodeManager::currentNM()->mkNode(kind::AND, finalLeft,
                                                           finalRight);
        return returnNode;
      }

    }
  } else {
    Node left = n[0];
    Node right = n[1];
    Node tempLeft = left;
    Node tempRight = right;
    Node returnNode;
    if(isConstQE(tempRight)) {
      Integer x = getIntegerFromNode(tempRight) + 1;
      tempRight = fromIntegerToNodeQE(x);
    } else {
      tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                   fromIntegerToNodeQE(1));
      tempRight = Rewriter::rewrite(tempRight);
    }
    Node finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                      tempRight);
    tempRight = right;
    if(isConstQE(tempLeft)) {
      Integer x = getIntegerFromNode(tempLeft) + 1;
      tempLeft = fromIntegerToNodeQE(x);
    } else {
      tempLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                  fromIntegerToNodeQE(1));
      tempLeft = Rewriter::rewrite(tempLeft);
    }
    Node finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                       tempLeft);
    returnNode = NodeManager::currentNM()->mkNode(kind::AND, finalLeft,
                                                  finalRight);
    return returnNode;
  }
}
Node QuantifierEliminate::replaceLTQE(Node n, Node bv) {
  if(n.hasBoundVar() && containsSameBoundVar(n, bv)) {
    Node left = n[0];
    Node right = n[1];
    Node shiftExpr;
    Node returnNode;
    if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
      if(isVarQE(left) || isVarWithCoefficientsQE(left)) {
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, left, right);
      } else {
        shiftExpr = getShiftedExpression(left, bv);
        left = separateBoundVarExpression(left, bv);
        if(!shiftExpr.isNull()) {
          right = NodeManager::currentNM()->mkNode(kind::PLUS, right,
                                                   shiftExpr);
        }
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, left, right);
      }
    } else {
      if(isVarQE(right) || isVarWithCoefficientsQE(right)) {
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, left, right);
      } else {
        shiftExpr = getShiftedExpression(right, bv);
        right = separateBoundVarExpression(right, bv);
        if(!shiftExpr.isNull()) {
          left = NodeManager::currentNM()->mkNode(kind::PLUS, left, shiftExpr);
        }
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, left, right);
      }
    }
    return returnNode;

  } else {
    Node left = n[0];
    Node right = n[1];
    Node returnNode = NodeManager::currentNM()->mkNode(kind::LT, left, right);
    return returnNode;
  }
}
Node QuantifierEliminate::replaceNegateLTQE(Node n, Node bv) {
  n = replaceGEQQE(n[0], bv);
  return n;
}
Node QuantifierEliminate::replaceNegateLEQQE(Node n, Node bv) {
  n = replaceGTQE(n[0], bv);
  return n;
}
Node QuantifierEliminate::replaceNegateGTQE(Node n, Node bv) {
  if(n[0].hasBoundVar() && containsSameBoundVar(n[0], bv)) {
    Node left = n[0][0];
    Node right = n[0][1];
    Node tempLeft;
    Node tempRight;
    Node returnNode;
    if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
      tempLeft = left;
      tempRight = right;
      if(tempLeft.getKind() == kind::PLUS
          || tempLeft.getKind() == kind::MINUS) {
        Node shiftedFromLeft = getShiftedExpression(tempLeft, bv);
        tempLeft = separateBoundVarExpression(tempLeft, bv);
        if(tempRight.getKind() == kind::PLUS
            || tempRight.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator rightBegin = tempRight.begin(), rightEnd =
              tempRight.end(); rightBegin != rightEnd; ++rightBegin) {
            Node childR = *rightBegin;
            if(isConstQE(childR)) {
              Integer x = getIntegerFromNode(childR);
              x = x + 1;
              TNode tn1 = childR;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempRight = tempRight.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, shiftedFromLeft,
                  fromIntegerToNodeQE(1));
            } else {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, fromIntegerToNodeQE(1));
            }
          } else {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(kind::PLUS,
                                                           tempRight,
                                                           shiftedFromLeft);
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempRight)) {
            Integer x = getIntegerFromNode(tempRight);
            x = x + 1;
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, shiftedFromLeft, fromIntegerToNodeQE(x));
            } else {
              tempRight = fromIntegerToNodeQE(x);
            }

          } else {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, shiftedFromLeft,
                  fromIntegerToNodeQE(1));
            } else {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, fromIntegerToNodeQE(1));
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        }

      } else {
        tempLeft = left;
        tempRight = right;
        if(tempRight.getKind() == kind::PLUS
            || tempRight.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator rightBegin = tempRight.begin(), rightEnd =
              tempRight.end(); rightBegin != rightEnd; ++rightBegin) {
            Node childR = *rightBegin;
            if(isConstQE(childR)) {
              Integer x = getIntegerFromNode(childR);
              x = x + 1;
              TNode tn1 = childR;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempRight = tempRight.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempRight)) {
            Integer x = getIntegerFromNode(tempRight);
            x = x + 1;
            tempRight = fromIntegerToNodeQE(x);
          }

          else {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        }
      }
    } else {
      tempLeft = left;
      tempRight = right;
      if(tempRight.getKind() == kind::PLUS
          || tempRight.getKind() == kind::MINUS) {
        Node shiftedFromRight = getShiftedExpression(tempRight, bv);
        tempRight = separateBoundVarExpression(tempRight, bv);
        if(tempLeft.getKind() == kind::PLUS
            || tempLeft.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator leftBegin = tempLeft.begin(), leftEnd =
              tempLeft.end(); leftBegin != leftEnd; ++leftBegin) {
            Node childL = *leftBegin;
            if(isConstQE(childL)) {
              Integer x = getIntegerFromNode(childL);
              x = x - 1;
              TNode tn1 = childL;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempLeft = tempLeft.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, shiftedFromRight,
                  fromIntegerToNodeQE(-1));
            } else {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
            }
          } else {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                          shiftedFromRight);
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempLeft)) {
            Integer x = getIntegerFromNode(tempLeft);
            x = x - 1;
            tempLeft = fromIntegerToNodeQE(x);
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                          shiftedFromRight);
            }
          } else {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, shiftedFromRight,
                  fromIntegerToNodeQE(-1));
            } else {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
            }
          }
        }
      } else {
        tempLeft = left;
        tempRight = right;
        if(tempLeft.getKind() == kind::PLUS
            || tempLeft.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator leftBegin = tempLeft.begin(), leftEnd =
              tempLeft.end(); leftBegin != leftEnd; ++leftBegin) {
            Node childL = *leftBegin;
            if(isConstQE(childL)) {
              Integer x = getIntegerFromNode(childL);
              x = x - 1;
              TNode tn1 = childL;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempLeft = tempLeft.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            tempLeft = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempLeft)) {
            Integer x = getIntegerFromNode(tempLeft);
            x = x - 1;
            tempLeft = fromIntegerToNodeQE(x);
          }

          else {
            tempLeft = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        }
      }

    }
    return returnNode;

  } else {
    Node left = n[0][0];
    Node right = n[0][1];
    if(isConstQE(right)) {
      Integer x = getIntegerFromNode(right) + 1;
      right = fromIntegerToNodeQE(x);
    } else {
      right = NodeManager::currentNM()->mkNode(kind::PLUS, right,
                                               fromIntegerToNodeQE(1));
      right = Rewriter::rewrite(right);
    }
    Node returnNode = NodeManager::currentNM()->mkNode(kind::LT, left, right);
    return returnNode;
  }
}
Node QuantifierEliminate::replaceNegateGEQQE(Node n, Node bv) {
  n = replaceLTQE(n[0], bv);
  return n;
}
Node QuantifierEliminate::replaceNegateEQUALQE(Node n, Node bv) {
  if(n[0].hasBoundVar() && containsSameBoundVar(n[0], bv)) {
    Node left = n[0][0];
    Node right = n[0][1];
    Node finalLeft;
    Node finalRight;
    if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
      Node tempLeft = left;
      Node tempRight = right;
      Node shiftFromLeft;
      if(isVarQE(left) || isVarWithCoefficientsQE(left)) {
        tempLeft = left;
      } else {
        shiftFromLeft = getShiftedExpression(tempLeft, bv);
        tempLeft = separateBoundVarExpression(tempLeft, bv);
      }
      if(!shiftFromLeft.isNull()) {
        tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                     shiftFromLeft);
      }
      finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                   tempRight);
      tempRight = right;
      if(!shiftFromLeft.isNull()) {
        tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                     shiftFromLeft);
      }
      finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                    tempLeft);
      Node returnNode = NodeManager::currentNM()->mkNode(kind::OR, finalLeft,
                                                         finalRight);
      return returnNode;
    } else {
      //right has boundvar bv
      Node tempLeft = left;
      Node tempRight = right;
      Node shiftFromRight;
      if(isVarQE(right) || isVarWithCoefficientsQE(right)) {
        tempRight = right;
      } else {
        shiftFromRight = getShiftedExpression(tempRight, bv);
        tempRight = separateBoundVarExpression(tempRight, bv);
      }
      if(!shiftFromRight.isNull()) {
        tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                    shiftFromRight);
      }
      finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                   tempRight);
      tempLeft = left;
      if(!shiftFromRight.isNull()) {
        tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                    shiftFromRight);
      }
      finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                    tempLeft);
      Node returnNode = NodeManager::currentNM()->mkNode(kind::OR, finalLeft,
                                                         finalRight);
      return returnNode;
    }
  } else {
    Node left = n[0];
    Node right = n[1];
    Node tempLeft = left;
    Node tempRight = right;
    Node returnNode;
    Node finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                      tempRight);
    Node finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                       tempLeft);
    returnNode = NodeManager::currentNM()->mkNode(kind::OR, finalLeft,
                                                  finalRight);
    return returnNode;
  }

}
Node QuantifierEliminate::replaceRelationOperatorQE(Node n, Node bv) {
  Node replaceNode;
  if(n.getKind() == kind::NOT) {
    Node temp = n[0];
    if(temp.getKind() == kind::LT) {
      replaceNode = replaceNegateLTQE(n, bv);
    } else if(temp.getKind() == kind::LEQ) {
      replaceNode = replaceNegateLEQQE(n, bv);
    } else if(temp.getKind() == kind::GT) {
      replaceNode = replaceNegateGTQE(n, bv);
    } else if(temp.getKind() == kind::GEQ) {
      replaceNode = replaceNegateGEQQE(n, bv);
    } else if(temp.getKind() == kind::EQUAL) {
      replaceNode = replaceNegateEQUALQE(n, bv);
    }
  } else if(n.getKind() == kind::LT) {
    replaceNode = replaceLTQE(n, bv);
  } else if(n.getKind() == kind::GT) {
    replaceNode = replaceGTQE(n, bv);
  } else if(n.getKind() == kind::LEQ) {
    replaceNode = replaceLEQQE(n, bv);
  } else if(n.getKind() == kind::GEQ) {
    replaceNode = replaceGEQQE(n, bv);
  } else if(n.getKind() == kind::EQUAL) {
    replaceNode = replaceEQUALQE(n, bv);
  }
  return replaceNode;
}

Node QuantifierEliminate::rewriteRelationOperatorQE(Node n, Node bv,
                                                    QuantifierEliminate q) {
  Node toReturn;
  std::vector<Node> replaceNode;
  Debug("expr-qetest")<<"Node n "<<n<<std::endl;
  Debug("expr-qetest")<<"bound var "<<bv<<std::endl;
  if(n.getKind() == kind::AND || n.getKind() == kind::OR) {
    for(Node::iterator i = n.begin(), iEnd = n.end(); i != iEnd; ++i) {
      Node c = *i;
      Debug("expr-qetest")<<"Node c "<<c<<std::endl;
      if(c.getKind() == kind::AND || c.getKind() == kind::OR) {
        toReturn = rewriteRelationOperatorQE(c, bv, q);
      } else {
        if((c.getKind() == kind::EQUAL && c[0].getKind() == kind::INTS_MODULUS)
            || (c.getKind() == kind::EQUAL
                && c[1].getKind() == kind::INTS_MODULUS)) {
          toReturn = c;
          Debug("expr-qetest")<<"No rewriting on divisibility node "<<toReturn<<std::endl;
        }
        else
        {
          toReturn = replaceRelationOperatorQE(c, bv);
          Debug("expr-qetest")<<"Node temp "<<toReturn<<std::endl;
        }
      }
      replaceNode.push_back(toReturn);
    }
    Node returnNode = NodeManager::currentNM()->mkNode(n.getKind(),
                                                       replaceNode);
    Debug("expr-qetest")<<"returnNode "<<returnNode<<std::endl;
    return returnNode;
  } else {
    Node returnNode = replaceRelationOperatorQE(n, bv);
    Debug("expr-qetest")<<"returnNode "<<returnNode<<std::endl;
    return returnNode;
  }
}
Node QuantifierEliminate::rewriteForSameCoefficients(Node n, Node bv,
                                                     QuantifierEliminate q) {
  Node t;
  if(n.getKind() == kind::NOT) {
    t = n[0];
    t = rewriteRelationOperatorQE(t, bv, q);
    Debug("expr-qetest")<<"rewrite relational operator result "<<t<<std::endl;
    n = parseEquation(t, bv, q);
    Debug("expr-qetest")<<"Parse equation result "<<t<<std::endl;
    return t.negate();
  } else {
    t = n;
    t = rewriteRelationOperatorQE(t, bv, q);
    Debug("expr-qetest")<<"rewrite relational operator result "<<t<<std::endl;
    t = parseEquation(t, bv, q);
    Debug("expr-qetest")<<"Parse equation result "<<t<<std::endl;
    return t;
  }
}

Node QuantifierEliminate::getExpressionWithDivisibility(Node n, Node bv,
                                                        QuantifierEliminate q) {
  Integer lcmVal = lcmValue;
  Debug("expr-qetest")<<"lcmValue in getDivisibility Expression "<<lcmVal<<std::endl;
  if(lcmVal > 1) {
    Node modulus = NodeManager::currentNM()->mkNode(
        kind::INTS_MODULUS, bv, fromIntegerToNodeQE(lcmVal));
    Node modulusExpr = NodeManager::currentNM()->mkNode(kind::EQUAL,
                                                        fromIntegerToNodeQE(0),
                                                        modulus);
    n = NodeManager::currentNM()->mkNode(kind::AND, n, modulusExpr);
    Debug("expr-qetest")<<"Final Node "<<n<<std::endl;
    return n;
  } else {
    return n;
  }
}

Node QuantifierEliminate::convertIFF(Node body) {
  Node nn = NodeManager::currentNM()->mkNode(
      kind::AND,
      NodeManager::currentNM()->mkNode(
          kind::OR, body[0].notNode(),
          body.getKind() == kind::XOR ? body[1].notNode() : body[1]),
      NodeManager::currentNM()->mkNode(
          kind::OR, body[0],
          body.getKind() == kind::XOR ? body[1] : body[1].notNode()));
  return nn;
}
Node QuantifierEliminate::computeSimpleITE(Node body) {
  if(body.getKind() == kind::EQUAL) {
    for(size_t i = 0; i < 2; i++) {
      if(body[i].getKind() == kind::ITE) {
        Node no = i == 0 ? body[1] : body[0];
        bool doRewrite = false;
        std::vector<Node> children;
        children.push_back(body[i][0]);
        for(size_t j = 1; j <= 2; j++) {
          //check if it rewrites to a constant
          Node nn = NodeManager::currentNM()->mkNode(kind::EQUAL, no,
                                                     body[i][j]);
          nn = Rewriter::rewrite(nn);
          children.push_back(nn);
          if(nn.isConst()) {
            doRewrite = true;
          }
        }
        if(doRewrite) {
          return NodeManager::currentNM()->mkNode(ITE, children);
        }
      }
    }
  } else if(body.getKind() != kind::APPLY_UF
      && body.getType() == NodeManager::currentNM()->booleanType()) {
    bool changed = false;
    std::vector<Node> children;
    for(size_t i = 0; i < body.getNumChildren(); i++) {
      Node nn = computeSimpleITE(body[i]);
      children.push_back(nn);
      changed = changed || nn != body[i];
    }
    if(changed) {
      return NodeManager::currentNM()->mkNode(body.getKind(), children);
    }
  }
  return body;
}

Node QuantifierEliminate::doRewriting(Node n, Node bv, QuantifierEliminate q) {
  Node t;
  Debug("expr-qetest")<<"kind of n "<<n.getKind()<<std::endl;
  t = eliminateImpliesQE(n);
  Debug("expr-qetest")<<"eliminate implies qe result "<<t<<std::endl;
  t = computeSimpleITE(t);
  Debug("expr-qetest")<<"perform simple ite lift "<<t<<std::endl;
  if(t.getKind() == kind::IFF || t.getKind() == kind::XOR) {
    t = convertIFF(t);
  }
  Debug("expr-qetest")<<"After iff conversion "<<t<<std::endl;
  t = convertToNNFQE(t);
  Debug("expr-qetest")<<"convert to nnf qe result "<<t<<std::endl;
  t = rewriteForSameCoefficients(t, bv, q);
  Debug("expr-qetest")<<"rewrite for same coefficients result "<<t<<std::endl;
  t = getExpressionWithDivisibility(t, bv, q);
  Debug("expr-qetest")<<"expression with divisibility result "<<t<<std::endl;
  return t;
}

Node QuantifierEliminate::replaceWithLeftInfinity(Node n, Node boundVar) {
  Debug("expr-qetest")<<"Node to evaluate infinity "<<n<<std::endl;
  Node returnNode;
  if(n[0].hasBoundVar() && containsSameBoundVar(n[0],boundVar))
  {
    Integer t = getIntegerFromNode(getCoefficientsOfExpression(n[0],boundVar));
    Debug("expr-qetest")<<"Coefficinet of n[0] "<<t<<std::endl;
    if(t < 0)
    {
      returnNode = mkBoolNode(false);
    }
    else
    {
      returnNode = mkBoolNode(true);
    }
  }
  else if(n[1].hasBoundVar() && containsSameBoundVar(n[1],boundVar))
  {
    Integer t = getIntegerFromNode(getCoefficientsOfExpression(n[1],boundVar));
    Debug("expr-qetest")<<"Coefficinet of n[1] "<<t<<std::endl;
    if(t < 0)
    {
      returnNode = mkBoolNode(true);
    }
    else
    {
      returnNode = mkBoolNode(false);
    }
  }
  else
  {
    returnNode = n;
  }
  return returnNode;
}
Node QuantifierEliminate::computeLeftProjection(Node n, Node bv) {
  Node toReturn;
  std::vector<Node> replaceNode;
  Debug("expr-qetest")<<"Expression in leftprojection "<<n<<std::endl;
  Debug("expr-qetest")<<"bound var "<<bv<<std::endl;
  if(n.getKind() == kind::AND || n.getKind() == kind::OR) {
    for(Node::iterator i = n.begin(), iEnd = n.end(); i != iEnd; ++i) {
      Node c = *i;
      Debug("expr-qetest")<<"Node c "<<c<<std::endl;
      if(c.getKind() == kind::AND || c.getKind() == kind::OR) {
        toReturn = computeLeftProjection(c, bv);
      } else {
        if((c.getKind() == kind::EQUAL && c[0].getKind() == kind::INTS_MODULUS)
            || (c.getKind() == kind::EQUAL
                && c[1].getKind() == kind::INTS_MODULUS)) {
          toReturn = c;
          Debug("expr-qetest")<<"No left infinity on divisibility node "<<toReturn<<std::endl;
        }
        else
        {
          toReturn = replaceWithLeftInfinity(c,bv);
          Debug("expr-qetest")<<"left inifinity "<<toReturn<<std::endl;
        }
      }
      replaceNode.push_back(toReturn);
    }
    for(int i = 0; i < (int) replaceNode.size(); i++) {
      Debug("expr-qetest")<<"replaceNode "<<i<<" "<<replaceNode[i]<<std::endl;
    }
    Node returnNode = NodeManager::currentNM()->mkNode(n.getKind(),
                                                       replaceNode);
    returnNode = Rewriter::rewrite(returnNode);
    Debug("expr-qetest")<<"return from left projection "<<returnNode<<std::endl;
    return returnNode;
  } else {
    Node returnNode = replaceWithLeftInfinity(n, bv);
    Debug("expr-qetest")<<"return from left projection "<<returnNode<<std::endl;
    return returnNode;
  }

}
Node QuantifierEliminate::replaceXForLeftProjection(Node n, Node original,
                                                    Integer rep) {
  TNode tn1 = n;
  Debug("expr-qetest")<<"TNode tn1 "<<tn1<<std::endl;
  Node f = fromIntegerToNodeQE(rep);
  TNode tn2 = f;
  Debug("expr-qetest")<<"TNode tn2 "<<tn2<<std::endl;
  original = original.substitute(tn1, tn2);
  Debug("expr-qetest")<<"Node original after substitution "<<original<<std::endl;
  return original;
}
Node QuantifierEliminate::computeXValueForLeftProjection(Node n,
                                                         Integer lcmCalc) {
  std::vector<Node> leftProjections;
  Node t = n;
  if(t.getKind() == kind::AND || t.getKind() == kind::OR
      || t.getKind() == kind::EQUAL) {
    Integer j = 1;
    while(j <= lcmCalc) {
      if(t.getKind() == kind::AND || t.getKind() == kind::OR) {
        std::vector<Node> innerLefts;
        for(Node::iterator leftP = t.begin(), leftEnd = t.end();
            leftP != leftEnd; ++leftP) {
          Node childLP = *leftP;
          if(childLP.getKind() == kind::EQUAL) {
            if(childLP[0].getKind() == kind::INTS_MODULUS) {
              childLP = replaceXForLeftProjection(childLP[0][0], childLP, j);
              childLP = Rewriter::rewrite(childLP);
              Integer x = getIntegerFromNode(childLP[0][0]);
              if(x.euclidianDivideRemainder(lcmCalc) == 1) {
                innerLefts.push_back(mkBoolNode(false));
              } else {
                innerLefts.push_back(mkBoolNode(true));
              }
            } else {
              childLP = replaceXForLeftProjection(childLP[1][0], childLP, j);
              childLP = Rewriter::rewrite(childLP);
              Integer x = getIntegerFromNode(childLP[1][0]);
              if(x.euclidianDivideRemainder(lcmCalc) == 1) {
                innerLefts.push_back(mkBoolNode(false));
              } else {
                innerLefts.push_back(mkBoolNode(true));
              }
            }
          } else {
          }
        }
        Node lp = NodeManager::currentNM()->mkNode(t.getKind(), innerLefts);
        lp = Rewriter::rewrite(lp);
        leftProjections.push_back(lp);
      } else {
        t = n;
        if(t[0].getKind() == kind::INTS_MODULUS) {
          t = replaceXForLeftProjection(t[0][0], t, j);
          t = Rewriter::rewrite(t);
          Integer y = getIntegerFromNode(t[0][0]);
          if(y.euclidianDivideRemainder(lcmCalc) == 1) {
            leftProjections.push_back(mkBoolNode(false));
          } else {
            leftProjections.push_back(mkBoolNode(true));
          }
        } else {
          t = replaceXForLeftProjection(t[1][0], t, j);
          t = Rewriter::rewrite(t);
          Integer y = getIntegerFromNode(t[1][0]);
          if(y.euclidianDivideRemainder(lcmCalc) == 1) {
            leftProjections.push_back(mkBoolNode(false));
          } else {
            leftProjections.push_back(mkBoolNode(true));
          }
        }
      }
      j = j + 1;
    }
    t = NodeManager::currentNM()->mkNode(kind::OR, leftProjections);
    t = Rewriter::rewrite(t);
    Debug("expr-qetest")<<"Final LeftProjection "<<t<<std::endl;
    return t;
  } else {
    return t;
  }
}
std::vector<Node> QuantifierEliminate::getMinimalExprForRightProjection(
    Node n, Node bv, std::vector<Node> bExpression) {
  Debug("expr-qetest")<<"Given Expression "<<n<<std::endl;
  Debug("expr-qetest")<<"Bound Variable "<<bv<<std::endl;
  Node toReturn;
  if(n.getKind() == kind::AND || n.getKind() == kind::OR) {
    for(Node::iterator i = n.begin(), iEnd = n.end(); i != iEnd; ++i) {
      Node c = *i;
      Debug("expr-qetest")<<"Node c "<<c<<std::endl;
      if(c.getKind() == kind::AND || c.getKind() == kind::OR) {
        bExpression = getMinimalExprForRightProjection(c,bv,bExpression);
      } else {
        if((c.getKind() == kind::EQUAL && c[0].getKind() == kind::INTS_MODULUS)
        || (c.getKind() == kind::EQUAL
            && c[1].getKind() == kind::INTS_MODULUS)) {
          toReturn = c;
          Debug("expr-qetest")<<"Not considering expression with divisibility "<<toReturn<<std::endl;
        }
        else
        {
          if(c[0].hasBoundVar() && containsSameBoundVar(c[0],bv))
          {
            Integer coeff = getIntegerFromNode(getCoefficientsOfExpression(c[0],bv));
            if(coeff<0)
            {
              toReturn = c[1];
              Debug("expr-qetest")<<"Node temp "<<toReturn<<std::endl;
              bExpression.push_back(c[1]);
            }
            else
            {}
          }
          else if(c[1].hasBoundVar() && containsSameBoundVar(c[1],bv))
          {
            Integer coeff = getIntegerFromNode(getCoefficientsOfExpression(c[1],bv));
            if(coeff > 0)
            {
              toReturn = c[0];
              Debug("expr-qetest")<<"Node temp "<<toReturn<<std::endl;
              bExpression.push_back(toReturn);
            }
            else {}
          }
        }
      }
    }
    if(bExpression.size() > 0 )
    {
      Debug("expr-qetest")<<"Multiple b's "<<toReturn<<std::endl;
      return bExpression;
    }
    else
    {
      Debug("expr-qetest")<<"No b's "<<toReturn<<std::endl;
      bExpression.push_back(mkBoolNode(false));
      return bExpression;
    }
  } else {
    if(n[0].hasBoundVar() && containsSameBoundVar(n[0],bv))
    {
      Integer coeff = getIntegerFromNode(getCoefficientsOfExpression(n[0],bv));
      if(coeff<0)
      {
        toReturn = n[1];
        Debug("expr-qetest")<<"Multiple b's "<<toReturn<<std::endl;
        bExpression.push_back(toReturn);
      }
      else {}
    }
    else if(n[1].hasBoundVar() && containsSameBoundVar(n[1],bv))
    {
      Integer coeff = getIntegerFromNode(getCoefficientsOfExpression(n[1],bv));
      if(coeff>0)
      {
        toReturn = n[0];
        Debug("expr-qetest")<<"Multiple b's "<<toReturn<<std::endl;
        bExpression.push_back(toReturn);
      }
      else {}
    }
    else
    {
      Debug("expr-qetest")<<"No b's "<<toReturn<<std::endl;
      bExpression.push_back(mkBoolNode(false));
    }
    return bExpression;
  }
}

Node QuantifierEliminate::replaceBoundVarRightProjection(Node n, TNode bExpr,
                                                         Node bv) {
  Debug("expr-qetest")<<"Given Expression "<<n<<std::endl;
  Node temp = n;
  /* Node toReturn;
   std::vector<Node> replaceNode;
   Debug("expr-qetest")<<"Expression in replace for right projection "<<n<<std::endl;
   Debug("expr-qetest")<<"bound var "<<bv<<std::endl;
   if(n.getKind() == kind::AND || n.getKind() == kind::OR) {
   for(Node::iterator i = n.begin(), iEnd = n.end(); i != iEnd; ++i) {
   Node c = *i;
   Debug("expr-qetest")<<"Node c "<<c<<std::endl;
   if(c.getKind() == kind::AND || c.getKind() == kind::OR) {
   toReturn = replaceBoundVarRightProjection(c, bExpr,bv);
   } else {
   if((c.getKind() == kind::EQUAL && c[0].getKind() == kind::INTS_MODULUS)
   || (c.getKind() == kind::EQUAL
   && c[1].getKind() == kind::INTS_MODULUS)) {
   toReturn = c;
   // Debug("expr-qetest")<<"No left infinity on divisibility node "<<toReturn<<std::endl;
   }
   else
   {
   toReturn = replaceWithLeftInfinity(c,bv);
   Debug("expr-qetest")<<"left inifinity "<<toReturn<<std::endl;
   }
   }
   replaceNode.push_back(toReturn);
   }
   Node returnNode = NodeManager::currentNM()->mkNode(n.getKind(),
   replaceNode);
   returnNode = Rewriter::rewrite(returnNode);
   Debug("expr-qetest")<<"return from left projection "<<returnNode<<std::endl;
   return returnNode;
   } else {
   Node returnNode = replaceWithLeftInfinity(n, bv);
   Debug("expr-qetest")<<"return from left projection "<<returnNode<<std::endl;
   return returnNode;
   }*/

  for(Node::iterator e_begin = n.begin(), e_end = n.end();
  e_begin != e_end;
  ++e_begin)
  {
    Node childE = *e_begin;
    Debug("expr-qetest")<<"childE in replacement rp "<<childE<<std::endl;
    if(childE.getKind() == kind::AND || childE.getKind() == kind::OR)
    {
      for(Node::iterator eInner_begin = childE.begin(), eInner_end = childE.end();
      eInner_begin != eInner_end;
      ++eInner_begin)
      {
        Node childE_inner = *eInner_begin;
        if(childE_inner[0].hasBoundVar() && containsSameBoundVar(childE_inner[0],bv))
        {
          if(isVarQE(childE_inner[0]))
          {
            TNode toReplace = childE_inner[0];
            temp = temp.substitute(toReplace,bExpr);
          }
          else if(isVarWithCoefficientsQE(childE_inner[0]))
          {
            Node var;
            if(getIntegerFromNode(childE_inner[0][0]) < 0)
            {
              var = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(-1),bExpr);
              var = Rewriter::rewrite(var);
            }
            else
            {
              var = bExpr;
            }
            TNode toReplace = childE_inner[0];
            TNode sub = var;
            temp = temp.substitute(toReplace,sub);
          }
          else
          {
            for(Node::iterator inner_begin = childE_inner[0].begin(),inner_end = childE_inner[0].end();
            inner_begin != inner_end;
            ++inner_begin)
            {
              Node innerExpression = *inner_begin;
              if(isVarQE(innerExpression))
              {
                TNode toReplace = innerExpression;
                temp = temp.substitute(toReplace,bExpr);
              }
              else if(isVarWithCoefficientsQE(innerExpression))
              {
                Node var;
                if(getIntegerFromNode(innerExpression[0]) < 0)
                {
                  var = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(-1),bExpr);
                  var = Rewriter::rewrite(var);
                }
                else
                {
                  var = bExpr;
                }
                TNode toReplace = innerExpression;
                TNode sub = var;
                temp = temp.substitute(toReplace,sub);
              }
              else
              {}
            }
          }
        }
        if(childE_inner[1].hasBoundVar() && containsSameBoundVar(childE_inner[1],bv))
        {
          if(isVarQE(childE_inner[1]))
          {
            TNode toReplace = childE_inner[1];
            temp = temp.substitute(toReplace,bExpr);
          }
          else if(isVarWithCoefficientsQE(childE_inner[1]))
          {
            Node var;
            if(getIntegerFromNode(childE_inner[1][0]) < 0)
            {
              var = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(-1),bExpr);
              var = Rewriter::rewrite(var);
            }
            else
            {
              var = bExpr;
            }
            TNode toReplace = childE_inner[1];
            TNode sub = var;
            temp = temp.substitute(toReplace,sub);
          }
          else
          {
            for(Node::iterator inner_begin = childE_inner[1].begin(),inner_end = childE_inner[1].end();
            inner_begin != inner_end;
            ++inner_begin)
            {
              Node innerExpression = *inner_begin;
              if(isVarQE(innerExpression))
              {
                TNode toReplace = innerExpression;
                temp = temp.substitute(toReplace,bExpr);
              }
              else if(isVarWithCoefficientsQE(innerExpression))
              {
                Node var;
                if(getIntegerFromNode(innerExpression[0]) < 0)
                {
                  var = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(-1),bExpr);
                  var = Rewriter::rewrite(var);
                }
                else
                {
                  var = bExpr;
                }
                TNode toReplace = innerExpression;
                TNode sub = var;
                temp = temp.substitute(toReplace,sub);
              }
              else
              {}
            }
          }
        }
      }
    }
    else if(childE.getKind() == kind::EQUAL)
    {
      for(int i=0;i<(int) childE.getNumChildren();i++)
      {
        if(childE[i].getKind() == kind::INTS_MODULUS)
        {
          if(childE[i][0].hasBoundVar() && containsSameBoundVar(childE[i][0],bv))
          {
            TNode toReplace = childE[i][0];
            temp = temp.substitute(toReplace,bExpr);
          }
        }
        else
        {}
      }
    }
    else
    {
      if(childE.hasBoundVar() && containsSameBoundVar(childE,bv))
      {
        TNode toReplace;
        if(isVarQE(childE))
        {
          toReplace = childE;
          temp = temp.substitute(toReplace,bExpr);
        }
        else if(isVarWithCoefficientsQE(childE))
        {
          Node var;
          Debug("expr-qetest")<<"Coefficient of childE "<<getIntegerFromNode(childE[0])<<std::endl;
          if(getIntegerFromNode(childE[0]) < 0)
          {
            var = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(-1),bExpr);
            var = Rewriter::rewrite(var);
          }
          else
          {
            var = bExpr;
          }
          Debug("expr-qetest")<<"var to replace "<<var<<std::endl;
          TNode toReplace = childE;
          TNode sub = var;
          temp = temp.substitute(toReplace,sub);
        }
        else
        {
          for(Node::iterator replaceRP = childE.begin(), replaceRPEnd = childE.end();
          replaceRP != replaceRPEnd;
          ++replaceRP)
          {
            Node rp = *replaceRP;
            if(isVarQE(rp) && containsSameBoundVar(rp,bv))
            {
              toReplace = rp;
              temp = temp.substitute(toReplace,bExpr);
              break;
            }
            else if(isVarWithCoefficientsQE(rp) && containsSameBoundVar(rp,bv))
            {
              Node var;
              if(getIntegerFromNode(rp[0]) < 0)
              {
                var = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(-1),bExpr);
                var = Rewriter::rewrite(var);
              }
              else
              {
                var = bExpr;
              }
              TNode toReplace = rp;
              TNode sub = var;
              temp = temp.substitute(toReplace,sub);
              break;
            }
            else {}
          }
        }
      }
      else
      {}
    }
  }
  return temp;
}
Node QuantifierEliminate::computeRightProjection(Node n, Node bv,
                                                 Integer lcmCalc) {
  std::vector<Node> bExpressions;
  std::vector < Node > test = getMinimalExprForRightProjection(n, bv,
                                                               bExpressions);
  for(int i = 0; i < (int) test.size(); i++) {
    Debug("expr-qetest")<<"b terms "<<test[i]<<std::endl;
  }
  Node result;
  Node rp;
  std::vector<Node> rightProjections;
  for(int i = 0; i < (int) test.size(); i++) {
    if(test[i] == mkBoolNode(false)) {
      result = test[i];
      Debug("expr-qetest")<<"Result After Replacement "<<result<<std::endl;
      return result;
    } else {
      Integer j = 1;
      TNode b;
      Integer lcm = lcmCalc;
      Debug("expr-qetest")<<"lcm in rp "<<lcm<<std::endl;
      Node bExpr;

      while(j <= lcm) {
        if(isConstQE(test[i])) {
          Integer y = getIntegerFromNode(test[i]) + j;
          bExpr = fromIntegerToNodeQE(y);
        } else {
          bExpr = NodeManager::currentNM()->mkNode(kind::PLUS, test[i],
                                                   fromIntegerToNodeQE(j));
          bExpr = Rewriter::rewrite(bExpr);
        }
        b = bExpr;
        Debug("expr-qetest")<<"before replacement b "<<b<<std::endl;
        rp = replaceBoundVarRightProjection(n, b, bv);
        Debug("expr-qetest")<<"after single b replacement rp "<<rp<<std::endl;
        rightProjections.push_back(rp);
        j = j + 1;
      }
    }
  }
  if(rightProjections.size() > 1) {
    result = NodeManager::currentNM()->mkNode(kind::OR, rightProjections);
    Debug("expr-qetest")<<"Result After Replacement "<<result<<std::endl;
  } else {
    result = rightProjections.back();
    Debug("expr-qetest")<<"Result After Replacement "<<result<<std::endl;
  }
  while(!rightProjections.empty()) {
    rightProjections.pop_back();
  }
  return result;
}
Node QuantifierEliminate::performCaseAnalysis(Node n, std::vector<Node> bv,
                                              QuantifierEliminate q) {
  Node var;
  Node left;
  Node right;
  Node temp;
  Node final;
  Node args = n;
  Integer qen = 1;
  Integer numOfQuantElim = q.getNumberOfQuantElim();
  while(bv.size() > 0) {
    Debug("expr-qetest")<<"qen in pca "<<qen<<std::endl;
    if(qen > numOfQuantElim) {
      Debug("expr-qetest")<<"Argument "<<args<<std::endl;
      if(args == mkBoolNode(true) || args == mkBoolNode(false)) {
      } else {
        Node v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, bv);
        Debug("expr-qetest")<<"v "<<v<<std::endl;
        std::vector<Node> children;
        children.push_back(v);
        children.push_back(args);
        args = NodeManager::currentNM()->mkNode(kind::FORALL, children);
      }
      break;
    } else {
      var = bv.back();
      if(var.getNumChildren() > 0) {
        var = var[0];
      }
      if(args == mkBoolNode(true) || args == mkBoolNode(false)) {
        while(!bv.empty()) {
          bv.pop_back();
        }
        break;
      }
      args = args.negate();
      args = convertToNNFQE(args);
      Debug("expr-qetest")<<"args before pca "<<args<<std::endl;
      args = doRewriting(args, var, q);
      Debug("expr-qetest")<<"After rewriting "<<args<<std::endl;
      Integer lcmCalc = lcmValue;
      temp = computeLeftProjection(args, var);
      left = computeXValueForLeftProjection(temp, lcmCalc);
      left = Rewriter::rewrite(left);
      Debug("expr-qetest")<<"left "<<left<<std::endl;
      right = computeRightProjection(args, var, lcmCalc);
      right = Rewriter::rewrite(right);
      Debug("expr-qetest")<<"right "<<right<<std::endl;
      if(left == mkBoolNode(false))
      {
        final = right;
      }
      else if(left == mkBoolNode(true))
      {
        if(right == mkBoolNode(false))
        {
          final = left;
        }
        else
        {
          final = NodeManager::currentNM()->mkNode(kind::OR, left, right);
        }
      }
      else
      {
        final = NodeManager::currentNM()->mkNode(kind::OR, left, right);
      }
      args = Rewriter::rewrite(final);
      Debug("expr-qetest")<<"args before second negation "<<args<<std::endl;
      args = args.negate();
      args = convertToNNFQE(args);
      args = Rewriter::rewrite(args);
      Debug("expr-qetest")<<"args after pca "<<args<<std::endl;
      bv.pop_back();
      qen = qen + 1;
    }
  }
  Debug("expr-qetest")<<"args "<<args<<std::endl;
  return args;
}

std::vector<Node> QuantifierEliminate::computeMultipleBoundVariables(Node n) {
  std::vector<Node> multipleBoundVars;
  Debug("expr-qetest")<<"n "<<n<<std::endl;
  if(n.getNumChildren() > 1) {
    for(int i = 0; i < (int) n.getNumChildren(); i++) {
      multipleBoundVars.push_back(n[i]);
    }
  } else {
    multipleBoundVars.push_back(n[0]);
  }
  return multipleBoundVars;
}
Node QuantifierEliminate::computeProjections(Node n, QuantifierEliminate q) {
  Node temp1;
  std::vector<Node> temp2;
  Node temp3;
  Node final;
  Node temp;
  Debug("expr-qetest")<<"Initial Node "<<n<<std::endl;
  Debug("expr-qetest")<<"Initial Node kind "<<n.getKind()<<std::endl;
  if(n.getKind() == kind::NOT) {
    negationDone = true;
    negateCount += 1;
    temp = n[0];
    if(temp.getKind() == kind::FORALL) {
      std::vector < Node > bv = computeMultipleBoundVariables(temp[0]);
      boundVar.push_back(bv);
      args.push_back(temp[1]);
      return computeProjections(temp[1], q);
    } else if(temp.getKind() == kind::AND) {
      std::vector<Node> miniscopedNode;
      Node result;
      std::vector<Node> bv_child;
      for(Node::iterator i = temp.begin(), i_end = temp.end(); i != i_end;
          ++i) {
        Node child = *i;
        if(child.getKind() == kind::FORALL) {
          bv_child = computeMultipleBoundVariables(child[0]);
          result = performCaseAnalysis(child[1], bv_child, q);
          miniscopedNode.push_back(result);
        } else {
        }
      }
      if(miniscopedNode.size() > 0) {
        Node newNode = NodeManager::currentNM()->mkNode(kind::AND,
                                                        miniscopedNode);
        Debug("expr-qetest")<<"newNode "<<newNode<<std::endl;
        args.push_back(newNode);
        Integer qen = 1;
        if(q.getNumberOfQuantElim() <= 0) {
          Debug("expr-qetest")<<"No quantifier to eliminate "<<std::endl;
          final = q.getOriginalExpression();
          while(!args.empty()) {
            args.pop_back();
          }
          while(!boundVar.empty())
          {
            boundVar.pop_back();
          }
          Debug("expr-qetest")<<"return from projection "<<final<<std::endl;
          return final;
        }
        else
        {
          bool bvc = false;
          while(!boundVar.empty()) {
            Debug("expr-qetest")<<"qen in cp "<<qen<<std::endl;
            if(qen > q.getNumberOfQuantElim())
            {
              bvc = true;
              Node a = args.back();
              Debug("expr-qetest")<<"Argument "<<a<<std::endl;
              std::vector<Node> b= boundVar.back();
              if(a == mkBoolNode(true) || a == mkBoolNode(false))
              {
                result = a;
              }
              else
              {
                Node var = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,b);
                Debug("expr-qetest")<<"var "<<var<<std::endl;
                std::vector<Node> children;
                children.push_back(var);
                children.push_back(a);
                result = NodeManager::currentNM()->mkNode(kind::FORALL,children);
              }
              while(!args.empty())
              {
                args.pop_back();
              }
              while(!boundVar.empty())
              {
                boundVar.pop_back();
              }
              break;
            }
            else
            {
              temp1 = args.back();
              Debug("expr-qetest")<<"args "<<temp1<<std::endl;
              temp2 = boundVar.back();
              result = performCaseAnalysis(temp1, temp2,q);
              boundVar.pop_back();
              while(!args.empty()) {
                args.pop_back();
              }
              if(result == mkBoolNode(true) || result == mkBoolNode(false)) {
                while(!boundVar.empty()) {
                  boundVar.pop_back();
                }
                args.push_back(result);
                qen = qen+1;
                break;
              } else {
                args.push_back(result);
                qen = qen+1;

              }
            }
          }
          if(bvc)
          {
            final = result;
          }
          else
          {
            result = args.back();
            final = result;
          }
          final = final.negate();
          while(!args.empty()) {
            args.pop_back();
          }
        }
      } else {
        Integer qen = 1;
        if(q.getNumberOfQuantElim() <= 0) {
          Debug("expr-qetest")<<"No quantifier to eliminate "<<std::endl;
          final = q.getOriginalExpression();
          while(!args.empty()) {
            args.pop_back();
          }
          while(!boundVar.empty())
          {
            boundVar.pop_back();
          }
          Debug("expr-qetest")<<"return from projection "<<final<<std::endl;
          return final;
        }
        else
        {
          bool bvc = false;
          while(!boundVar.empty()) {
            Debug("expr-qetest")<<"qen in cp "<<qen<<std::endl;
            if(qen > q.getNumberOfQuantElim())
            {
              bvc = true;
              Node a = args.back();
              Debug("expr-qetest")<<"Argument "<<a<<std::endl;
              std::vector<Node> b= boundVar.back();
              if(a == mkBoolNode(true) || a == mkBoolNode(false))
              {
                result = a;
              }
              else
              {
                Node var = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,b);
                Debug("expr-qetest")<<"var "<<var<<std::endl;
                std::vector<Node> children;
                children.push_back(var);
                children.push_back(a);
                result = NodeManager::currentNM()->mkNode(kind::FORALL,children);
              }
              while(!args.empty())
              {
                args.pop_back();
              }
              while(!boundVar.empty())
              {
                boundVar.pop_back();
              }
              break;

            }
            else
            {
              temp1 = args.back();
              Debug("expr-qetest")<<"args "<<temp1<<std::endl;
              temp2 = boundVar.back();
              result = performCaseAnalysis(temp1, temp2,q);
              boundVar.pop_back();
              while(!args.empty()) {
                args.pop_back();
              }
              if(result == mkBoolNode(true) || result == mkBoolNode(false)) {
                while(!boundVar.empty()) {
                  boundVar.pop_back();
                }
                args.push_back(result);
                qen = qen+1;
                break;
              } else {
                args.push_back(result);
                qen = qen+1;
              }
            }
          }
          if(bvc)
          {
            final = result;
          }
          else
          {
            result = args.back();
            final = result;
          }
          final = final.negate();
          while(!args.empty()) {
            args.pop_back();
          }
        }
      }
    } else {
      Debug("expr-qetest")<<"pca called from inside not "<<std::endl;
      Integer qen = 1;
      if(q.getNumberOfQuantElim() <= 0) {
        Debug("expr-qetest")<<"No quantifier to eliminate "<<std::endl;
        final = q.getOriginalExpression();
        while(!args.empty()) {
          args.pop_back();
        }
        while(!boundVar.empty())
        {
          boundVar.pop_back();
        }
        Debug("expr-qetest")<<"return from projection "<<final<<std::endl;
        return final;
      }
      else
      {
        if(boundVar.size() > 0) {
          Node result3;
          bool bvc = false;
          while(!boundVar.empty()) {
            Debug("expr-qetest")<<"qen in cp "<<qen<<std::endl;
            if(qen > q.getNumberOfQuantElim())
            {
              bvc = true;
              Node a = args.back();
              Debug("expr-qetest")<<"Argument "<<a<<std::endl;
              std::vector<Node> b= boundVar.back();
              if(a == mkBoolNode(true) || a == mkBoolNode(false))
              {
                result3 = a;
              }
              else
              {
                Node var = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,b);
                Debug("expr-qetest")<<"var "<<var<<std::endl;
                std::vector<Node> children;
                children.push_back(var);
                children.push_back(a);
                result3 = NodeManager::currentNM()->mkNode(kind::FORALL,children);
              }
              while(!args.empty())
              {
                args.pop_back();
              }
              while(!boundVar.empty())
              {
                boundVar.pop_back();
              }
              break;

            }
            else
            {
              temp1 = args.back();
              Debug("expr-qetest")<<"args "<<temp1<<std::endl;
              temp2 = boundVar.back();
              result3 = performCaseAnalysis(temp1, temp2,q);
              boundVar.pop_back();
              while(!args.empty()) {
                args.pop_back();
              }
              if(result3 == mkBoolNode(true) || result3 == mkBoolNode(false)) {
                while(!boundVar.empty()) {
                  boundVar.pop_back();
                }
                args.push_back(result3);
                qen = qen +1;
                break;
              } else {
                args.push_back(result3);
                qen = qen +1;
              }
            }
          }
          if(bvc)
          {
            final = result3;
          }
          else
          {
            result3 = args.back();
            final = result3;
          }
          if(negationDone && (negateCount.euclidianDivideRemainder(2) == 0))
          {
            final = final.negate();
          }
          while(!args.empty()) {
            args.pop_back();
          }
        } else {
          final = n;
        }
      }

    }
  } else if(n.getKind() == kind::FORALL) {
    std::vector < Node > bv = computeMultipleBoundVariables(n[0]);
    args.push_back(n[1]);
    boundVar.push_back(bv);
    if(n[1].getKind() == kind::NOT) {
      return computeProjections(n[1][0],q);
    } else {
      return computeProjections(n[1],q);
    }
  } else if(n.getKind() == kind::AND) {
    std::vector<Node> miniscopedNode1;
    Node result1;
    std::vector<Node> bv_child1;
    for(Node::iterator j = n.begin(), j_end = n.end(); j != j_end; ++j) {
      Node child1 = *j;
      if(child1.getKind() == kind::FORALL) {
        bv_child1 = computeMultipleBoundVariables(child1[0]);
        Debug("expr-qetest")<<"Bound var in miniscoping "<<bv_child1.size()<<std::endl;
        result1 = performCaseAnalysis(child1[1], bv_child1,q);
        miniscopedNode1.push_back(result1);
      } else {
      }
    }
    if(miniscopedNode1.size() > 0) {
      Node newNode1 = NodeManager::currentNM()->mkNode(kind::AND,
      miniscopedNode1);
      Debug("expr-qetest")<<"newNode1 "<<newNode1<<std::endl;
      args.push_back(newNode1);
      Integer qen = 1;
      if(q.getNumberOfQuantElim() <= 0) {
        Debug("expr-qetest")<<"No quantifier to eliminate "<<std::endl;
        final = q.getOriginalExpression();
        while(!args.empty()) {
          args.pop_back();
        }
        while(!boundVar.empty())
        {
          boundVar.pop_back();
        }
        Debug("expr-qetest")<<"return from projection "<<final<<std::endl;
        return final;
      }
      else
      {
        bool bvc = false;
        while(!boundVar.empty()) {
          Debug("expr-qetest")<<"qen in cp "<<qen<<std::endl;
          if(qen > q.getNumberOfQuantElim())
          {
            bvc = false;
            Node a = args.back();
            Debug("expr-qetest")<<"Argument "<<a<<std::endl;
            std::vector<Node> b= boundVar.back();
            if(a == mkBoolNode(true) || a == mkBoolNode(false))
            {
              result1 = a;
            }
            else
            {
              Node var = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,b);
              Debug("expr-qetest")<<"var "<<var<<std::endl;
              std::vector<Node> children;
              children.push_back(var);
              children.push_back(a);
              result1 = NodeManager::currentNM()->mkNode(kind::FORALL,children);
            }
            while(!args.empty())
            {
              args.pop_back();
            }
            while(!boundVar.empty())
            {
              boundVar.pop_back();
            }
            break;
          }
          else
          {
            temp1 = args.back();
            Debug("expr-qetest")<<"args"<<temp1<<std::endl;
            temp2 = boundVar.back();
            result1 = performCaseAnalysis(temp1, temp2,q);
            boundVar.pop_back();
            while(!args.empty()) {
              args.pop_back();
            }
            if(result1 == mkBoolNode(true) || result1 == mkBoolNode(false)) {
              while(!boundVar.empty()) {
                boundVar.pop_back();
              }
              args.push_back(result1);
              qen = qen + 1;
              break;
            } else {
              args.push_back(result1);
              qen = qen + 1;
            }
          }
        }
        if(bvc)
        {
          final = result1;
        }
        else
        {
          result1 = args.back();
          final = result1;
        }
        Debug("expr-qetest")<<"result1 "<<result1<<std::endl;
        while(!args.empty()) {
          args.pop_back();
        }
      }
    } else {
      Debug("expr-qetest")<<"pca called from outside not "<<std::endl;
      Integer qen = 1;
      if(q.getNumberOfQuantElim() <= 0) {
        Debug("expr-qetest")<<"No quantifier to eliminate "<<std::endl;
        final = q.getOriginalExpression();
        while(!args.empty()) {
          args.pop_back();
        }
        while(!boundVar.empty())
        {
          boundVar.pop_back();
        }
        Debug("expr-qetest")<<"return from projection "<<final<<std::endl;
        return final;
      }
      else
      {
        bool bvc = false;
        while(!boundVar.empty()) {
          Debug("expr-qetest")<<"qen in cp "<<qen<<std::endl;
          if(qen > q.getNumberOfQuantElim())
          {
            bvc = false;
            Node a = args.back();
            Debug("expr-qetest")<<"Argument "<<a<<std::endl;
            std::vector<Node> b= boundVar.back();
            if(a == mkBoolNode(true) || a == mkBoolNode(false))
            {
              result1 = a;
            }
            else
            {
              Node var = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,b);
              Debug("expr-qetest")<<"var "<<var<<std::endl;
              std::vector<Node> children;
              children.push_back(var);
              children.push_back(a);
              result1 = NodeManager::currentNM()->mkNode(kind::FORALL,children);
            }
            while(!args.empty())
            {
              args.pop_back();
            }
            while(!boundVar.empty())
            {
              boundVar.pop_back();
            }
            break;
          }
          else
          {
            temp1 = args.back();
            Debug("expr-qetest")<<"args"<<temp1<<std::endl;
            temp2 = boundVar.back();
            result1 = performCaseAnalysis(temp1, temp2,q);
            boundVar.pop_back();
            while(!args.empty()) {
              args.pop_back();
            }
            if(result1 == mkBoolNode(true) || result1 == mkBoolNode(false)) {
              while(!boundVar.empty()) {
                boundVar.pop_back();
              }
              args.push_back(result1);
              qen = qen + 1;
              break;
            } else {
              args.push_back(result1);
              qen = qen + 1;
            }
          }

        }
        if(bvc)
        {
          final = result1;
        }
        else
        {
          result1 = args.back();
          final = result1;
        }
        while(!args.empty()) {
          args.pop_back();
        }
        Debug("expr-qetest")<<"result1 "<<result1<<std::endl;
      }

    }
  } else {
    Integer qen = 1;
    if(q.getNumberOfQuantElim() <= 0) {
      Debug("expr-qetest")<<"No quantifier to eliminate "<<std::endl;
      final = q.getOriginalExpression();
      while(!args.empty()) {
        args.pop_back();
      }
      while(!boundVar.empty())
      {
        boundVar.pop_back();
      }
      Debug("expr-qetest")<<"return from projection "<<final<<std::endl;
      return final;
    }
    if(boundVar.size() > 0) {
      Node result2;
      bool bvc = false;
      while(!boundVar.empty()) {
        Debug("expr-qetest")<<"qen in cp "<<qen<<std::endl;
        if(qen > q.getNumberOfQuantElim())
        {
          bvc = true;
          Node a = args.back();
          Debug("expr-qetest")<<"Argument "<<a<<std::endl;
          std::vector<Node> b= boundVar.back();
          if(a == mkBoolNode(true) || a == mkBoolNode(false))
          {
            result2 = a;
          }
          else
          {
            Node var = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,b);
            Debug("expr-qetest")<<"var "<<var<<std::endl;
            std::vector<Node> children;
            children.push_back(var);
            children.push_back(a);
            result2 = NodeManager::currentNM()->mkNode(kind::FORALL,children);
          }
          while(!args.empty())
          {
            args.pop_back();
          }
          while(!boundVar.empty())
          {
            boundVar.pop_back();
          }
          break;
        }
        else
        {
          temp1 = args.back();
          Debug("expr-qetest")<<"args "<<temp1<<std::endl;
          temp2 = boundVar.back();
          result2 = performCaseAnalysis(temp1, temp2,q);
          boundVar.pop_back();
          while(!args.empty()) {
            args.pop_back();
          }
          if(result2 == mkBoolNode(true) || result2 == mkBoolNode(false)) {
            while(!boundVar.empty()) {
              boundVar.pop_back();
            }
            args.push_back(result2);
            qen = qen + 1;
            break;
          } else {
            args.push_back(result2);
            qen = qen + 1;
          }
        }

      }
      if(bvc)
      {
        final = result2;
      }
      else
      {
        result2 = args.back();
      }
      Debug("expr-qetest")<<"result2 "<<result2<<std::endl;
      if(negationDone && (negateCount.euclidianDivideRemainder(2) == 1))
      {
        final = result2.negate();
      }
      else
      {
        final = result2;
      }
      while(!args.empty()) {
        args.pop_back();
      }
    } else {
      final = n;
    }
  }
  final = Rewriter::rewrite(final);
  Debug("expr-qetest")<<"return from projection "<<final<<std::endl;
  return final;
}
void QuantifierEliminate::setOriginalExpression(Node n) {
  this->originalExpression = n;
}
Node QuantifierEliminate::getOriginalExpression() {
  return this->originalExpression;
}
void QuantifierEliminate::setNumberOfQuantElim(int x) {
  this->numOfQuantiferToElim = x;
}
Integer QuantifierEliminate::getNumberOfQuantElim() {
  return this->numOfQuantiferToElim;
}
std::vector<ExpressionContainer> QuantifierEliminate::getExpContainer(
    QuantifierEliminate q) {
  return q.expressionContainer;
}
void QuantifierEliminate::setEquivalentExpression(Node n) {
  this->equivalentExpression = n;
}
Node QuantifierEliminate::getEquivalentExpression() {
  return this->equivalentExpression;
}
void QuantifierEliminate::setMessage(std::string s) {
  this->successMessage = s;
}
std::string QuantifierEliminate::getMessage() {
  return this->successMessage;
}
void QuantifierEliminate::setOptionQE(std::string opt) {
  this->option = opt;
}
std::string QuantifierEliminate::getOptionQE() {
  return this->option;
}
bool QuantifierEliminate::checkType(Node n) {
  Debug("expr-qetest")<<"Given Node "<<n<<std::endl;
  Node check;
  TypeNode t;
  bool b = true;
  if(n.getNumChildren() > 1)
  {
    for(int i=0;i<(int) n.getNumChildren();i++)
    {
      if(n[i].getNumChildren() > 0)
      {
        check = n[i][0];
      }
      else
      {
        check = n[i];
      }
      t = check.getType();
      if(!t.isInteger())
      {
        b = false;
        break;
      }
    }
  }
  else
  {
    t = n[0].getType();
    if(!t.isInteger())
    {
      b = false;
    }
    else
    {
      b = true;
    }
  }
  Debug("expr-qetest")<<"checkType "<<b<<std::endl;
  return b;
}
Node QuantifierEliminate::boundVarTypeChecker(Node n) {
  Debug("expr-qetest")<<"Given Expression  "<<n<<std::endl;
  Node t;
  bool check;
  Node toReturn;
  if(n.getKind() == kind::NOT)
  {
    t = n[0];
    if(t.getKind() == kind::FORALL)
    {
      check = checkType(t[0]);
      if(!check)
      {
        toReturn = mkBoolNode(false);
        return toReturn;
      }
      else
      {
        return boundVarTypeChecker(t[1]);
      }
    }
    else if(t.getKind() == kind::AND)
    {
      for(Node::iterator mBegin = t.begin(),mEnd = t.end();
      mBegin != mEnd;
      ++mBegin)
      {
        Node child = *mBegin;
        if(child.getKind() == kind::FORALL)
        {
          check = checkType(child[0]);
          if(!check)
          {
            toReturn = mkBoolNode(false);
            return toReturn;
          }
          else
          {
            return boundVarTypeChecker(child[1]);
          }
        }
        else
        {
          return boundVarTypeChecker(child);
        }
      }
    }
    else
    {
      if(t == mkBoolNode(true) || t == mkBoolNode(false))
      {
        return t;
      }
      else
      {
        TypeNode t1;
        for(Node::iterator nBegin = t.begin(),nEnd = t.end();
        nBegin != nEnd;
        ++nBegin)
        {
          Node c = *nBegin;
          Debug("expr-qetest")<<"c in not  "<<c<<std::endl;
          if(isVarQE(c))
          {
            t1 = c.getType();
            if(!t1.isInteger())
            {
              toReturn = mkBoolNode(false);
              return toReturn;
            }
          }
          else if(isVarWithCoefficientsQE(c))
          {
            Debug("expr-qetest")<<"isVarWithCoefficientsQE in not "<<c<<std::endl;
            t1 = c[1].getType();
            Debug("expr-qetest")<<"typenode t1 "<<t1<<std::endl;
            if(!t1.isInteger())
            {
              toReturn = mkBoolNode(false);
              return toReturn;
            }
          }
          else if(isConstQE(c))
          {
            t1 = c.getType();
            Debug("expr-qetest")<<"typenode t1 "<<t1<<std::endl;
            if(!t1.isInteger())
            {
              toReturn = mkBoolNode(false);
              return toReturn;
            }
          }
          else
          {
            Debug("expr-qetest")<<"exp in not "<<c<<std::endl;
            toReturn = boundVarTypeChecker(c);
          }
        }
      }

    }
  }
  else if(n.getKind() == kind::FORALL)
  {
    check = checkType(n[0]);
    if(!check)
    {
      toReturn = mkBoolNode(false);
      return toReturn;
    }
    else
    {
      return boundVarTypeChecker(n[1]);
    }
  }
  else if(n.getKind() == kind::AND)
  {
    for(Node::iterator pBegin = n.begin(),pEnd = n.end();
    pBegin != pEnd;
    ++pBegin)
    {
      Node child1 = *pBegin;

      if(child1.getKind() == kind::FORALL)
      {
        check = checkType(child1[0]);
        if(!check)
        {
          toReturn = mkBoolNode(false);
          return toReturn;
        }
        else
        {
          return boundVarTypeChecker(child1[1]);
        }
      }
      else
      {
        return boundVarTypeChecker(child1);
      }
    }
  }
  else
  {
    if(n == mkBoolNode(true) || n == mkBoolNode(false))
    {
      return n;
    }
    else
    {
      TypeNode t2;
      for(Node::iterator qBegin = n.begin(),qEnd = n.end();
      qBegin != qEnd;
      ++qBegin)
      {
        Node c1 = *qBegin;
        Debug("expr-qetest")<<"c1  "<<c1<<std::endl;
        if(isVarQE(c1))
        {
          t2 = c1.getType();
          if(!t2.isInteger())
          {
            toReturn = mkBoolNode(false);
            return toReturn;
          }
        }
        else if(isVarWithCoefficientsQE(c1))
        {
          Debug("expr-qetest")<<"isVarWithCoefficientsQE  "<<c1<<std::endl;
          t2 = c1[1].getType();
          Debug("expr-qetest")<<"typenode t2 "<<t2<<std::endl;
          if(!t2.isInteger())
          {
            toReturn = mkBoolNode(false);
            return toReturn;
          }
        }
        else if(isConstQE(c1))
        {
          t2 = c1.getType();
          Debug("expr-qetest")<<"typenode t2 "<<t2<<std::endl;
          if(!t2.isInteger())
          {
            toReturn = mkBoolNode(false);
            return toReturn;
          }
        }
        else
        {
          Debug("expr-qetest")<<"exp "<<c1<<std::endl;
          toReturn = boundVarTypeChecker(c1);
        }
      }
    }

  }
  Debug("expr-qetest")<<"toReturn "<<toReturn<<std::endl;
  if(toReturn.isNull())
  {
    return mkBoolNode(true);
  }
  else
  {
    return toReturn;
  }

}

Node QuantifierEliminate::prenexChecker(Node n) {
  Node toReturn;
  if(n.getKind() == kind::NOT) {
    Node t = n[0];
    if(t.getKind() == kind::FORALL) {
      return prenexChecker(t[1]);
    } else if(t.getKind() == kind::AND) {
      for(Node::iterator nBegin = n.begin(), nEnd = n.end(); nBegin != nEnd;
          ++nBegin) {
        Node c1 = *nBegin;
        if(c1.getKind() == kind::FORALL) {
          return prenexChecker(c1[1]);
        } else {
          return prenexChecker(c1);
        }
      }
    } else {
      for(Node::iterator qBegin = t.begin(), qEnd = t.end(); qBegin != qEnd;
          ++qBegin) {
        Node child1 = *qBegin;
        if((child1.getKind() == kind::NOT && child1[0].getKind() == kind::FORALL)
            || (child1.getKind() == kind::FORALL)) {
          toReturn = mkBoolNode(false);
          return toReturn;
        } else {
          toReturn = prenexChecker(child1);
        }
      }
    }
  } else if(n.getKind() == kind::FORALL) {
    return prenexChecker(n[1]);
  } else if(n.getKind() == kind::AND) {
    for(Node::iterator mBegin = n.begin(), mEnd = n.end(); mBegin != mEnd;
        ++mBegin) {
      Node c = *mBegin;
      if(c.getKind() == kind::FORALL) {
        return prenexChecker(c[1]);
      } else {
        return prenexChecker(c);
      }
    }
  } else {
    for(Node::iterator pBegin = n.begin(), pEnd = n.end(); pBegin != pEnd;
        ++pBegin) {
      Node child = *pBegin;
      if((child.getKind() == kind::NOT && child[0].getKind() == kind::FORALL)
          || (child.getKind() == kind::FORALL)) {
        toReturn = mkBoolNode(false);
        return toReturn;
      } else {
        toReturn = prenexChecker(child);
      }
    }
  }
  Debug("expre-qetest")<<"toReturn from prenex checker "<<toReturn<<std::endl;
  return toReturn;
}
std::vector<Node> QuantifierEliminate::getBoundVariablesList(
    Node n, std::vector<Node> boundVars) {
  Node t;
  if(n.getKind() == kind::NOT) {
    t = n[0];
    if(t.getKind() == kind::AND) {
      for(Node::iterator it = t.begin(), it_end = t.end(); it != it_end; ++it) {
        Node child = *it;
        if(child.getKind() == kind::FORALL) {
          std::vector < Node > bv = computeMultipleBoundVariables(child[0]);
          for(int i = 0; i < (int) bv.size(); i++) {
            if(bv[i].getNumChildren() > 0) {
              //boundVars.insert(bv[i][0]);
              boundVars.push_back(bv[i][0]);
            } else {
              //boundVars.insert(bv[i]);
              boundVars.push_back(bv[i]);
            }
          }
        } else {
        }
      }
      return boundVars;
    } else if(t.getKind() == kind::FORALL) {
      std::vector < Node > bv = computeMultipleBoundVariables(t[0]);
      for(int i = 0; i < (int) bv.size(); i++) {
        if(bv[i].getNumChildren() > 0) {
         // boundVars.insert(bv[i][0]);
          boundVars.push_back(bv[i][0]);
        } else {
         // boundVars.insert(bv[i]);
          boundVars.push_back(bv[i]);
        }
      }
      return getBoundVariablesList(t[1], boundVars);
    } else {
      return boundVars;
    }

  } else if(n.getKind() == kind::AND) {

    for(Node::iterator it = n.begin(), it_end = n.end(); it != it_end; ++it) {
      Node child = *it;
      if(child.getKind() == kind::FORALL) {
        std::vector < Node > bv = computeMultipleBoundVariables(child[0]);
        for(int i = 0; i < (int) bv.size(); i++) {
          if(bv[i].getNumChildren() > 0) {
            boundVars.push_back(bv[i][0]);
          } else {
            boundVars.push_back(bv[i]);
          }
        }
      } else {
      }
    }
    return boundVars;

  } else if(n.getKind() == kind::FORALL) {
    std::vector < Node > bv = computeMultipleBoundVariables(n[0]);
    for(int i = 0; i < (int) bv.size(); i++) {
      if(bv[i].getNumChildren() > 0) {
        boundVars.push_back(bv[i][0]);
      } else {
        boundVars.push_back(bv[i]);
      }
    }
    return getBoundVariablesList(n[1], boundVars);
  } else {
    return boundVars;
  }
}
std::vector<Node> QuantifierEliminate::obtainFreeVariable(Node n,
                                                          std::vector<Node> v) {
  Node toReturn;
  for(Node::iterator i = n.begin(), i_end = n.end(); i != i_end; ++i) {
    Node c = *i;
    if(c.isVar() && c.getKind() != kind::BOUND_VARIABLE) {
      toReturn = c;
      v.push_back(toReturn);
    } else {
      v = obtainFreeVariable(c, v);
    }
  }
  return v;
}
std::set<Node> QuantifierEliminate::getFreeVariablesList(Node n,
                                                         std::set<Node> fv) {
  Node t;
  if(n.getKind() == kind::NOT) {
    t = n[0];
  } else {
    t = n;
  }
  if(t.getKind() == kind::AND || t.getKind() == kind::OR) {
    for(Node::iterator it = t.begin(), it_end = t.end(); it != it_end; ++it) {
      Node child = *it;
      if(child.getKind() == kind::AND || child.getKind() == kind::OR
          || child.getKind() == kind::NOT) {
        fv = getFreeVariablesList(child, fv);
      } else {
        std::vector<Node> vars;
        vars = obtainFreeVariable(child, vars);
        for(int i = 0; i < (int) vars.size(); i++) {
          fv.insert(vars[i]);
        }
      }
    }
    return fv;
  } else {
    std::vector<Node> vars;
    vars = obtainFreeVariable(t, vars);
    for(int i = 0; i < (int) vars.size(); i++) {
      fv.insert(vars[i]);
    }
    return fv;
  }
}
Node QuantifierEliminate::extractQuantifierFreeFormula(Node n) {
  Node t;
  if(n.getKind() == kind::NOT && n[0].getKind() == kind::FORALL) {
    t = extractQuantifierFreeFormula(n[0][1]);
  } else if(n.getKind() == kind::FORALL) {
    t = extractQuantifierFreeFormula(n[1]);
  } else {
    t = n;
  }
  return t;
}

Node QuantifierEliminate::evaluateExpressionOnAssignment(
    Node n, std::map<Node, Node> assignment) {
  Node temp = n;
  std::map<Node,Node>::iterator it = assignment.begin();
  std::map<Node,Node>::iterator it1 = assignment.begin();
  while(it!= assignment.end())
  {
    it1 = assignment.find(it->first);
    if(it1 == assignment.end())
    {
      continue;
    }
    else
    {
      TNode tn1 = it->first;
      TNode tn2 = it->second;
      temp = temp.substitute(tn1,tn2);
      ++it;
    }
  }
  temp = Rewriter::rewrite(temp);
  return temp;
}

std::vector<Node> QuantifierEliminate::mkStrongerExpression2(
    Node n, std::map<Node, Node> assignment, std::vector<Node> inner_expr) {
  Node toReturn;
  if(n.getKind() == kind::AND) {
    for(Node::iterator i = n.begin(), i_end = n.end(); i != i_end; ++i) {
      Node child = *i;
      if(child.getKind() == kind::AND || child.getKind() == kind::OR) {
        inner_expr = mkStrongerExpression2(child, assignment, inner_expr);
      } else {
        toReturn = child;
        inner_expr.push_back(child);
      }
    }
  } else{
    for(Node::iterator j = n.begin(), j_end = n.end(); j != j_end; ++j) {
      Node child1 = *j;
      if(child1.getKind() == kind::AND || child1.getKind() == kind::OR) {
        inner_expr = mkStrongerExpression2(child1, assignment, inner_expr);
      } else {
        toReturn = evaluateExpressionOnAssignment(child1, assignment);
        if(toReturn == mkBoolNode(true)) {
          inner_expr.push_back(child1);
          break;
        }
        else
        {}
      }
    }
  }
  return inner_expr;
}

Node QuantifierEliminate::mkStrongerExpression(
    Node n, std::map<Node, Node> assignment) {
  std::vector<Node> inner_expr;
  std::vector<Node> temp;
  if(n.getKind() == kind::AND || n.getKind() == kind::OR)
  {
    temp = mkStrongerExpression2(n,assignment,inner_expr);
    Node returnNode = NodeManager::currentNM()->mkNode(n.getKind(),temp);
    return returnNode;
  }
  else
  {
    return n;
  }
}

Node QuantifierEliminate::strongerQEProcedure(Node n, QuantifierEliminate qe) {

  NodeTemplate<true> x(n);
  Node t = extractQuantifierFreeFormula(x);
  t = eliminateImpliesQE(t);
  t = convertToNNFQE(t);
  t = Rewriter::rewrite(t);
  t = computeSimpleITE(t);
  if(t.getKind() == kind::IFF || t.getKind() == kind::XOR) {
    t = convertIFF(t);
  }
  Debug("expr-qetest")<<"After rewriting "<<t<<std::endl;
  Expr test = t.toExpr();
  ExprManager *em1 = t.toExpr().getExprManager();
  SmtEngine smt(em1);
  SmtScope smts(&smt);
  smt.setLogic("LIA");
  smt.setOption("produce-models", true);
  smt.setOption("finite-model-find", true);
  Type integer = em1->integerType();
  std::vector<Node> boundVars;
  std::set<Node> vars;
  std::vector < Node > bv = getBoundVariablesList(x, boundVars);
  std::set<Node> v = getFreeVariablesList(t, vars);
  std::vector<Expr> variables;
  for(int i=0;i<(int)bv.size();i++)
  {
    Debug("expr-qetest")<<"Boundvars "<<bv[i]<<std::endl;
    if(bv[i].isVar() && bv[i].getKind() == kind::BOUND_VARIABLE)
    {
      variables.push_back(bv[i].toExpr());
    }
  }
  for(std::set<Node>::iterator it = v.begin(); it != v.end(); ++it) {
    Debug("expr-qetest")<<"free vars "<<*it<<std::endl;
    Node child = *it;
    if(child.isVar() && child.getKind() != kind::BOUND_VARIABLE)
    {
      variables.push_back(child.toExpr());
    }
  }
  Result result = smt.checkSat(test);
  std::map<Node, Node> assignment;
  std::map<Node, Node>::iterator map_insert = assignment.begin();
  for(int i = 0; i < (int) variables.size(); i++) {
    assignment.insert(
        map_insert,
        std::pair<Node, Node>(NodeTemplate<true>(variables[i]),
                              NodeTemplate<true>(smt.getValue(variables[i]))));
  }

  for(map_insert = assignment.begin(); map_insert != assignment.end();
      ++map_insert) {
    Debug("expr-qetest")<<map_insert->first<<" => "<<map_insert->second<<std::endl;
  }
  Node strongerExpression = mkStrongerExpression(t, assignment);
  Debug("expr-qetest")<<"stronger expression without quantifiers "<<strongerExpression<<std::endl;
  Node var = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,bv);
  Debug("expr-qetest")<<"var "<<var<<std::endl;
  std::vector<Node> children;
  children.push_back(var);
  children.push_back(strongerExpression);
  Node inputExpr = NodeManager::currentNM()->mkNode(kind::FORALL,children);
  if(n.getKind() == kind::NOT)
  {
    inputExpr = inputExpr.notNode();
  }
  Debug("expr-qetest")<<"stronger expression with quantifiers "<<inputExpr<<std::endl;
  Node returnNode = computeProjections(inputExpr,qe);
  return returnNode;
}

Node QuantifierEliminate::defautlQEProcedure(Node n, QuantifierEliminate qe) {
  Node returnNode = computeProjections(n, qe);
  return returnNode;
}

QuantifierEliminate QuantifierEliminate::qeEngine(Node n, int numOfQuantifiers,
                                                  std::string optionQE) {
  Debug("expr-qetest")<<"Before qeEngine  "<<n<<std::endl;
  Debug("expr-qetest")<<"Before qeEnine kind "<<n.getKind()<<std::endl;
  QuantifierEliminate qe;
  qe.setOriginalExpression(n);
  qe.setNumberOfQuantElim(numOfQuantifiers);
  qe.setOptionQE(optionQE);
  Node temp = n;
  temp = Rewriter::rewrite(temp);
  Node final;
  bool typeCheck,prenexCheck;
  if(numOfQuantifiers <= 0)
  {
    std::stringstream sstm;
    sstm << "(error! Number of quantifiers requested to be eliminated is " << numOfQuantifiers <<" )";
    std::string s = sstm.str();
    Debug("expr-qetest")<<s<<std::endl;
    qe.setMessage(s);
    qe.setEquivalentExpression(qe.getOriginalExpression());
    return qe;
  }
  else
  {
    if(boundVarTypeChecker(temp) == mkBoolNode(false))
    {
      typeCheck = false;
    }
    else
    {
      typeCheck = true;
    }
    if(prenexChecker(temp) == mkBoolNode(false))
    {
      prenexCheck = false;
    }
    else
    {
      prenexCheck = true;
    }
    if(typeCheck && prenexCheck)
    {
      Debug("expr-qetest")<<"Type checker has found no problem "<<std::endl;
      Debug("expr-qetest")<<"Prenex checker has found no problem "<<std::endl;
      Debug("expr-qetest")<<"Before computeProjections expression "<<temp<<std::endl;
      if(qe.getOptionQE() == "weak")
      {
        std::string m = "(weak version of qe not yet implemented )";
        Debug("expr-qetest")<<m<<std::endl;
        qe.setMessage(m);
        qe.setEquivalentExpression(qe.getOriginalExpression());
        return qe;
      }
      else if(qe.getOptionQE() == "strong")
      {
        if(temp == mkBoolNode(true) || temp == mkBoolNode(false))
        {
          Debug("expr-qetest")<<"Type checker has found no problem "<<std::endl;
          Debug("expr-qetest")<<"Prenex checker has found no problem "<<std::endl;
          final = computeProjections(temp,qe);
          Debug("expr-qetest")<<"After qe "<<final<<std::endl;
          qe.setEquivalentExpression(final);
          qe.setMessage("success");
          return qe;
        }
        else
        {
          Node t = strongerQEProcedure(temp,qe);
          qe.setEquivalentExpression(t);
          qe.setMessage("success");
          return qe;
        }

      }
      else
      {
        if(temp == mkBoolNode(true) || temp == mkBoolNode(false))
        {
          Debug("expr-qetest")<<"Type checker has found no problem "<<std::endl;
          Debug("expr-qetest")<<"Prenex checker has found no problem "<<std::endl;
          final = computeProjections(temp,qe);
          Debug("expr-qetest")<<"After qe "<<final<<std::endl;
          qe.setEquivalentExpression(final);
          qe.setMessage("success");
          return qe;
        }
        else
        {
          final = strongerQEProcedure(temp,qe);
          Debug("expr-qetest")<<"After qe "<<final<<std::endl;
          qe.setEquivalentExpression(final);
          qe.setMessage("success");
          return qe;
        }
      }
    }
    else if(!typeCheck)
    {
      Debug("expr-qetest")<<"Type checker failure contains non integer type "<<std::endl;
      qe.setMessage("(Input expression contains non integer type)");
      qe.setEquivalentExpression(qe.getOriginalExpression());
      return qe;
    }
    else
    {
      Debug("expr-qetest")<<"Expression not in prenex form "<<std::endl;
      qe.setMessage("(Input expression not in prenex form)");
      qe.setEquivalentExpression(qe.getOriginalExpression());
      return qe;
    }
  }
}

