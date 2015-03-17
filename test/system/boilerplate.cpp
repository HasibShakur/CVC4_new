/*********************                                                        */
/*! \file boilerplate.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A simple start-up/tear-down test for CVC4.
 **
 ** This simple test just makes sure that the public interface is
 ** minimally functional.  It is useful as a template to use for other
 ** system tests.
 **/

#include <iostream>
#include <sstream>

#include "expr/expr.h"
#include "smt/smt_engine.h"

using namespace CVC4;
using namespace std;

int main() {
  ExprManager em;
  Options opts;
  SmtEngine smt(&em);
  Result r = smt.query(em.mkConst(true));

  return (Result::VALID == r) ? 0 : 1;
}
