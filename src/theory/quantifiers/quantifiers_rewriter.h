/*********************                                                        */
/*! \file quantifiers_rewriter.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Rewriter for the theory of inductive quantifiers
 **
 ** Rewriter for the theory of inductive quantifiers.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H
#define __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H

#include "theory/rewriter.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class QuantifiersRewriter {
public:
  static bool isClause( Node n );
  static bool isLiteral( Node n );
  static bool isCube( Node n );
private:
  static void addNodeToOrBuilder( Node n, NodeBuilder<>& t );
  static Node mkForAll( std::vector< Node >& args, Node body, Node ipl );
  static void computeArgs( std::vector< Node >& args, std::map< Node, bool >& activeMap, Node n );
  static void computeArgVec( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n );
  static void computeArgVec2( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n, Node ipl );
  static bool hasArg( std::vector< Node >& args, Node n );
  static bool hasArg1( Node a, Node n );
  static Node computeClause( Node n );
private:
  static Node computeElimSymbols( Node body );
  static Node computeMiniscoping( Node f, std::vector< Node >& args, Node body, Node ipl );
  static Node computeAggressiveMiniscoping( std::vector< Node >& args, Node body );
  static Node computeNNF( Node body );
  static Node computeProcessIte( Node body, bool hasPol, bool pol );
  static Node computeVarElimination( Node body, std::vector< Node >& args, Node& ipl );
  static Node computeCNF( Node body, std::vector< Node >& args, NodeBuilder<>& defs, bool forcePred );
  static Node computePrenex( Node body, std::vector< Node >& args, bool pol );
  static Node computeSplit( Node f, Node body, std::vector< Node >& args );
private:
  enum{
    COMPUTE_ELIM_SYMBOLS = 0,
    COMPUTE_MINISCOPING,
    COMPUTE_AGGRESSIVE_MINISCOPING,
    COMPUTE_NNF,
    COMPUTE_PROCESS_ITE,
    COMPUTE_PRENEX,
    COMPUTE_VAR_ELIMINATION,
    //COMPUTE_FLATTEN_ARGS_UF,
    COMPUTE_CNF,
    COMPUTE_SPLIT,
    COMPUTE_LAST
  };
  static Node computeOperation( Node f, bool isNested, int computeOption );
public:
  static RewriteResponse preRewrite(TNode in);
  static RewriteResponse postRewrite(TNode in);
  static inline void init() {}
  static inline void shutdown() {}
private:
  /** options */
  static bool doMiniscopingNoFreeVar();
  static bool doMiniscopingAnd();
  static bool doOperation( Node f, bool isNested, int computeOption );
public:
  static Node rewriteRewriteRule( Node r );
  static bool containsQuantifiers(Node n);
  static Node preSkolemizeQuantifiers(Node n, bool polarity, std::vector< TypeNode >& fvTypes, std::vector<TNode>& fvs);
};/* class QuantifiersRewriter */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H */

