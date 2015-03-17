#include "cvc4_public.h"

#ifndef __CVC4__EXPR_QUANTIFIERELIMINATE_H
#define __CVC4__EXPR_QUANTIFIERELIMINATE_H

#include<iostream>
#include<vector>
#include<set>
#include<map>
#include "expr/node.h"
#include "smt/smt_engine.h"
#include "theory/arith/normal_form.h"
namespace CVC4 {
class Container;
class ExpressionContainer;
class CVC4_PUBLIC QuantifierEliminate {
private:
  //static variables

  static std::vector<std::vector<Node> > boundVar;
  static std::vector<Node> args;
  static Integer lcmValue;
  static std::vector<Container> container;
  static bool negationDone;
  static Integer negateCount;

  //non static variables
  Integer numOfQuantiferToElim;
  Node originalExpression;
  std::string successMessage;
  Node equivalentExpression;
  std::string option;

  std::vector<ExpressionContainer> expressionContainer;

  //static methods

  static Node convertToNNFQE(Node body);
  static std::vector<Node> computeMultipleBoundVariables(Node n);
  static bool isLiteralQE(Node body);
  static bool isConstQE(Node n);
  static bool isVarQE(Node n);
  static bool isVarWithCoefficientsQE(Node n);
  static bool isEquationQE(Node n);
  static bool isRelationalOperatorTypeQE(Kind k);
  static Integer getIntegerFromNode(Node n);
  static Node fromIntegerToNodeQE(Integer n);
  static bool containsSameBoundVar(Node n, Node bv);
  static Integer lcmQE(Integer a, Integer b);
  static Node getShiftedExpression(Node n, Node bv);
  static Node separateBoundVarExpression(Node n, Node bv);
  static Node performCaseAnalysis(Node n, std::vector<Node> bv,
                                  QuantifierEliminate q);
  static Node computeProjections(Node n, QuantifierEliminate q);
  static Node computeXValueForLeftProjection(Node n, Integer lcmCalc);
  static Node parseEquation(Node n, Node bv, QuantifierEliminate q);
  static Node computeLeftProjection(Node n, Node bv);
  static Node computeRightProjection(Node n, Node bv, Integer lcmCalc);
  static Node doRewriting(Node n, Node bv, QuantifierEliminate q);
  static Node eliminateImpliesQE(Node body);
  static Node convertIFF(Node body);
  static Node computeSimpleITE(Node body);
  static std::vector<Node> getMinimalExprForRightProjection(Node n, Node bv,std::vector<Node> bExpressions);
  static Node rewriteForSameCoefficients(Node n, Node boundVar,
                                         QuantifierEliminate q);
  static void parseCoefficientQE(Node n, QuantifierEliminate q);
  static Node multiplyEquationWithLcm(Node n,Node bv);
  static Node multiplyIndividualExpression(Node n,Node bv,Integer multiple,std::vector<Node> expr);
  static Integer calculateLCMofCoeff(std::vector<Integer> coeffs);
  static Node rewriteRelationOperatorQE(Node n, Node bv, QuantifierEliminate q);
  static Node replaceRelationOperatorQE(Node n, Node bv);
  static Node replaceGTQE(Node n, Node bv);
  static Node replaceGEQQE(Node n, Node bv);
  static Node replaceLEQQE(Node n, Node bv);
  static Node replaceEQUALQE(Node n, Node bv);
  static Node replaceLTQE(Node n, Node bv);
  static Node replaceNegateLTQE(Node n, Node bv);
  static Node replaceNegateLEQQE(Node n, Node bv);
  static Node replaceNegateGTQE(Node n, Node bv);
  static Node replaceNegateGEQQE(Node n, Node bv);
  static Node replaceNegateEQUALQE(Node n, Node bv);
  static Integer getLcmResult(Node t, Node bv, QuantifierEliminate q);
  static Node getExpressionWithDivisibility(Node n, Node bv,
                                            QuantifierEliminate q);
  static Node replaceBoundVarRightProjection(Node n, TNode bExpr, Node bv);
  static Node replaceXForLeftProjection(Node n, Node original, Integer rep);
  static Node boundVarTypeChecker(Node n);
  static bool checkType(Node n);
  static Node prenexChecker(Node n);
  static Node getCoefficientsOfExpression(Node n,Node bv);
  static Node replaceWithLeftInfinity(Node n,Node boundVar);
  static std::set<Node> getBoundVariablesList(Node n,std::set<Node> bv);
  static std::set<Node> getFreeVariablesList(Node n,std::set<Node> bv);
  static std::vector<Node> obtainFreeVariable(Node n,std::vector<Node> vars);
  static Node extractQuantifierFreeFormula(Node n);
  static Node strongerQEProcedure(Node n,QuantifierEliminate qe);
  static Node defautlQEProcedure(Node n,QuantifierEliminate qe);
 // static Node mkDeepCopy(Node n,ExprManager *em);
 // static Node copyInternalNodes(Node n,std::vector<Node> internalExp,ExprManager *em);
  static std::vector<Node> mkStrongerExpression2(Node n,std::map<Node,Node> assignment,std::vector<Node> inner_expr);
  static Node mkStrongerExpression(Node n,std::map<Node,Node> assignment);
  static Node evaluateExpressionOnAssignment(Node n,std::map<Node,Node> assignment);
  //non static methods

  std::vector<ExpressionContainer> getExpContainer(QuantifierEliminate q);
  void setOriginalExpression(Node n);
  void setNumberOfQuantElim(int x);
  void setMessage(std::string s);
  void setEquivalentExpression(Node n);
  void setOptionQE(std::string opt);

public:

  //static public functions
  static QuantifierEliminate qeEngine(Node n, int numOfQuantifiers, std::string optionQE);

  //non static public functions

  Node getOriginalExpression();
  Integer getNumberOfQuantElim();
  std::string getMessage();
  Node getEquivalentExpression();
  std::string getOptionQE();

};

class Container {
private:
  Node variable;
  Integer coefficient;
public:
  Container(Node v, Integer c) {
    variable = v;
    coefficient = c;
  }
  Node getVariable() {
    return variable;
  }
  Integer getCoefficient() {
    return coefficient;
  }
  void setCoefficient(Integer c) {
    coefficient = c;
  }
};
class ExpressionContainer {
private:
  Node expression;
  Integer multiplier;
public:
  ExpressionContainer(Node e, Integer i) {
    expression = e;
    multiplier = i;
  }
  Node getExpression() {
    return expression;
  }
  Integer getMultiplier() {
    return multiplier;
  }
  void setExpression(Node e) {
    expression = e;
  }
  void setMultiplier(Integer i) {
    multiplier = i;
  }

};
}
#endif
