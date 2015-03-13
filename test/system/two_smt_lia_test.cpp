#include <iostream>
#include <sstream>

#include "expr/expr.h"
#include "smt/smt_engine.h"
#include "util/integer.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/normal_form.h"

using namespace CVC4;
using namespace CVC4::expr;
using namespace std;

int main() {
  ExprManager em;
  Options opts;
  SmtEngine smt(&em);
  //SmtEngine smt2(&em);
  smt.setLogic("LIA");
  smt.setOption("produce-models", true);
 // smt.setOption("finite-model-find", true);
  Type integer = em.integerType();
  Expr y = em.mkVar("y",integer);
  Expr x = em.mkVar("x",integer);
  Expr two = em.mkConst(Rational(2));
  Expr two_x = em.mkExpr(kind::MULT,two,x);
  Expr exp1 = em.mkExpr(kind::EQUAL,y,two_x);
  Result r1 = smt.checkSat(exp1);
  std::cout<<"x => "<<smt.getValue(x)<<std::endl;
  std::cout<<"y => "<<smt.getValue(y)<<std::endl;

  SmtEngine smt2(&em);
  smt2.setLogic("LIA");
  smt2.setOption("produce-models", true);

  Expr exp2 = em.mkExpr(kind::MULT,two,smt.getValue(x));
  Expr exp3 = em.mkExpr(kind::EQUAL,smt.getValue(y),exp2);
  Result r2 = smt2.query(exp3);
  std::cout<<"final "<<r2.toString()<<std::endl;

  return 0;
}
