/*********************                                                        */
/*! \file theory_uf_strong_solver.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of theory uf strong solver class
 **/

#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/term_database.h"
#include "theory/uf/options.h"
#include "theory/theory_model.h"
#include "theory/quantifiers/symmetry_breaking.h"

//#define ONE_SPLIT_REGION
//#define DISABLE_QUICK_CLIQUE_CHECKS
//#define COMBINE_REGIONS_SMALL_INTO_LARGE

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

void StrongSolverTheoryUF::SortModel::Region::addRep( Node n ) {
  setRep( n, true );
}

void StrongSolverTheoryUF::SortModel::Region::takeNode( StrongSolverTheoryUF::SortModel::Region* r, Node n ){
  Assert( !hasRep( n ) );
  Assert( r->hasRep( n ) );
  //add representative
  setRep( n, true );
  //take disequalities from r
  RegionNodeInfo* rni = r->d_nodes[n];
  for( int t=0; t<2; t++ ){
    RegionNodeInfo::DiseqList* del = rni->d_disequalities[t];
    for( NodeBoolMap::iterator it = del->d_disequalities.begin(); it != del->d_disequalities.end(); ++it ){
      if( (*it).second ){
        r->setDisequal( n, (*it).first, t, false );
        if( t==0 ){
          if( hasRep( (*it).first ) ){
            setDisequal( (*it).first, n, 0, false );
            setDisequal( (*it).first, n, 1, true );
            setDisequal( n, (*it).first, 1, true );
          }else{
            setDisequal( n, (*it).first, 0, true );
          }
        }else{
          r->setDisequal( (*it).first, n, 1, false );
          r->setDisequal( (*it).first, n, 0, true );
          setDisequal( n, (*it).first, 0, true );
        }
      }
    }
  }
  //remove representative
  r->setRep( n, false );
}

void StrongSolverTheoryUF::SortModel::Region::combine( StrongSolverTheoryUF::SortModel::Region* r ){
  //take all nodes from r
  for( std::map< Node, RegionNodeInfo* >::iterator it = r->d_nodes.begin(); it != r->d_nodes.end(); ++it ){
    if( it->second->d_valid ){
      setRep( it->first, true );
    }
  }
  for( std::map< Node, RegionNodeInfo* >::iterator it = r->d_nodes.begin(); it != r->d_nodes.end(); ++it ){
    if( it->second->d_valid ){
      //take disequalities from r
      Node n = it->first;
      RegionNodeInfo* rni = it->second;
      for( int t=0; t<2; t++ ){
        RegionNodeInfo::DiseqList* del = rni->d_disequalities[t];
        for( NodeBoolMap::iterator it2 = del->d_disequalities.begin(); it2 != del->d_disequalities.end(); ++it2 ){
          if( (*it2).second ){
            if( t==0 && hasRep( (*it2).first ) ){
              setDisequal( (*it2).first, n, 0, false );
              setDisequal( (*it2).first, n, 1, true );
              setDisequal( n, (*it2).first, 1, true );
            }else{
              setDisequal( n, (*it2).first, t, true );
            }
          }
        }
      }
    }
  }
  r->d_valid = false;
}

/** setEqual */
void StrongSolverTheoryUF::SortModel::Region::setEqual( Node a, Node b ){
  Assert( hasRep( a ) && hasRep( b ) );
  //move disequalities of b over to a
  for( int t=0; t<2; t++ ){
    RegionNodeInfo::DiseqList* del = d_nodes[b]->d_disequalities[t];
    for( NodeBoolMap::iterator it = del->d_disequalities.begin(); it != del->d_disequalities.end(); ++it ){
      if( (*it).second ){
        Node n = (*it).first;
        //get the region that contains the endpoint of the disequality b != ...
        Region* nr = d_cf->d_regions[ d_cf->d_regions_map[ n ] ];
        if( !isDisequal( a, n, t ) ){
          setDisequal( a, n, t, true );
          nr->setDisequal( n, a, t, true );
          //notify the disequality propagator
          if( options::ufssDiseqPropagation() ){
            d_cf->d_thss->getDisequalityPropagator()->assertDisequal(a, n, Node::null());
          }
          if( options::ufssSymBreak() ){
            d_cf->d_thss->getSymmetryBreaker()->assertDisequal( a, n );
          }
        }
        setDisequal( b, n, t, false );
        nr->setDisequal( n, b, t, false );
      }
    }
  }
  //remove b from representatives
  setRep( b, false );
}

void StrongSolverTheoryUF::SortModel::Region::setDisequal( Node n1, Node n2, int type, bool valid ){
  //Debug("uf-ss-region-debug") << "set disequal " << n1 << " " << n2 << " " << type << " " << valid << std::endl;
  //debugPrint("uf-ss-region-debug");
  //Assert( isDisequal( n1, n2, type )!=valid );
  if( isDisequal( n1, n2, type )!=valid ){    //DO_THIS: make assertion
    d_nodes[ n1 ]->d_disequalities[type]->setDisequal( n2, valid );
    if( type==0 ){
      d_total_diseq_external = d_total_diseq_external + ( valid ? 1 : -1 );
    }else{
      d_total_diseq_internal = d_total_diseq_internal + ( valid ? 1 : -1 );
      if( valid ){
        //if they are both a part of testClique, then remove split
        if( d_testClique.find( n1 )!=d_testClique.end() && d_testClique[n1] &&
            d_testClique.find( n2 )!=d_testClique.end() && d_testClique[n2] ){
          Node eq = NodeManager::currentNM()->mkNode( EQUAL, n1, n2 );
          if( d_splits.find( eq )!=d_splits.end() && d_splits[ eq ] ){
            Debug("uf-ss-debug") << "removing split for " << n1 << " " << n2 << std::endl;
            d_splits[ eq ] = false;
            d_splitsSize = d_splitsSize - 1;
          }
        }
      }
    }
  }
}

void StrongSolverTheoryUF::SortModel::Region::setRep( Node n, bool valid ){
  Assert( hasRep( n )!=valid );
  if( valid && d_nodes.find( n )==d_nodes.end() ){
    d_nodes[n] = new RegionNodeInfo( d_cf->d_thss->getSatContext() );
  }
  d_nodes[n]->d_valid = valid;
  d_reps_size = d_reps_size + ( valid ? 1 : -1 );
  //removing a member of the test clique from this region
  if( d_testClique.find( n )!=d_testClique.end() && d_testClique[n] ){
    Assert( !valid );
    d_testClique[n] = false;
    d_testCliqueSize = d_testCliqueSize - 1;
    //remove all splits involving n
    for( NodeBoolMap::iterator it = d_splits.begin(); it != d_splits.end(); ++it ){
      if( (*it).second ){
        if( (*it).first[0]==n || (*it).first[1]==n ){
          d_splits[ (*it).first ] = false;
          d_splitsSize = d_splitsSize - 1;
        }
      }
    }
  }
}

bool StrongSolverTheoryUF::SortModel::Region::isDisequal( Node n1, Node n2, int type ){
  RegionNodeInfo::DiseqList* del = d_nodes[ n1 ]->d_disequalities[type];
  return del->d_disequalities.find( n2 )!=del->d_disequalities.end() && del->d_disequalities[n2];
}

struct sortInternalDegree {
  StrongSolverTheoryUF::SortModel::Region* r;
  bool operator() (Node i,Node j) { return (r->d_nodes[i]->getNumInternalDisequalities()>r->d_nodes[j]->getNumInternalDisequalities());}
};

struct sortExternalDegree {
  StrongSolverTheoryUF::SortModel::Region* r;
  bool operator() (Node i,Node j) { return (r->d_nodes[i]->getNumExternalDisequalities()>r->d_nodes[j]->getNumExternalDisequalities());}
};

int gmcCount = 0;

bool StrongSolverTheoryUF::SortModel::Region::getMustCombine( int cardinality ){
  if( options::ufssRegions() && d_total_diseq_external>=long(cardinality) ){
    //The number of external disequalities is greater than or equal to cardinality.
    //Thus, a clique of size cardinality+1 may exist between nodes in d_regions[i] and other regions
    //Check if this is actually the case:  must have n nodes with outgoing degree (cardinality+1-n) for some n>0
    std::vector< int > degrees;
    for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
      RegionNodeInfo* rni = it->second;
      if( rni->d_valid ){
        if( rni->getNumDisequalities()>=cardinality ){
          int outDeg = rni->getNumExternalDisequalities();
          if( outDeg>=cardinality ){
            //we have 1 node of degree greater than (cardinality)
            return true;
          }else if( outDeg>=1 ){
            degrees.push_back( outDeg );
            if( (int)degrees.size()>=cardinality ){
              //we have (cardinality) nodes of degree 1
              return true;
            }
          }
        }
      }
    }
    gmcCount++;
    if( gmcCount%100==0 ){
      Trace("gmc-count") << gmcCount << " " << cardinality << " sample : " << degrees.size() << std::endl;
    }
    //this should happen relatively infrequently....
    std::sort( degrees.begin(), degrees.end() );
    for( int i=0; i<(int)degrees.size(); i++ ){
      if( degrees[i]>=cardinality+1-((int)degrees.size()-i) ){
        return true;
      }
    }
  }
  return false;
}

bool StrongSolverTheoryUF::SortModel::Region::check( Theory::Effort level, int cardinality, std::vector< Node >& clique ){
  if( d_reps_size>long(cardinality) ){
    if( d_total_diseq_internal==d_reps_size*( d_reps_size - 1 ) ){
      if( d_reps_size>1 ){
        //quick clique check, all reps form a clique
        for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
          if( it->second->d_valid ){
            clique.push_back( it->first );
          }
        }
        Trace("quick-clique") << "Found quick clique" << std::endl;
        return true;
      }else{
        return false;
      }
    }else if( options::ufssRegions() || options::ufssEagerSplits() || level==Theory::EFFORT_FULL ){
      //build test clique, up to size cardinality+1
      if( d_testCliqueSize<=long(cardinality) ){
        std::vector< Node > newClique;
        if( d_testCliqueSize<long(cardinality) ){
          for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
            //if not in the test clique, add it to the set of new members
            if( it->second->d_valid && ( d_testClique.find( it->first )==d_testClique.end() || !d_testClique[ it->first ] ) ){
              //if( it->second->getNumInternalDisequalities()>cardinality || level==Theory::EFFORT_FULL ){
              newClique.push_back( it->first );
              //}
            }
          }
          //choose remaining nodes with the highest degrees
          sortInternalDegree sidObj;
          sidObj.r = this;
          std::sort( newClique.begin(), newClique.end(), sidObj );
          newClique.erase( newClique.begin() + ( cardinality - d_testCliqueSize ) + 1, newClique.end() );
        }else{
          //scan for the highest degree
          int maxDeg = -1;
          Node maxNode;
          for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
            //if not in the test clique, add it to the set of new members
            if( it->second->d_valid && ( d_testClique.find( it->first )==d_testClique.end() || !d_testClique[ it->first ] ) ){
              if( it->second->getNumInternalDisequalities()>maxDeg ){
                maxDeg = it->second->getNumInternalDisequalities();
                maxNode = it->first;
              }
            }
          }
          Assert( maxNode!=Node::null() );
          newClique.push_back( maxNode );
        }
        //check splits internal to new members
        for( int j=0; j<(int)newClique.size(); j++ ){
          Debug("uf-ss-debug") << "Choose to add clique member " << newClique[j] << std::endl;
          for( int k=(j+1); k<(int)newClique.size(); k++ ){
            if( !isDisequal( newClique[j], newClique[k], 1 ) ){
              d_splits[ NodeManager::currentNM()->mkNode( EQUAL, newClique[j], newClique[k] ) ] = true;
              d_splitsSize = d_splitsSize + 1;
            }
          }
          //check disequalities with old members
          for( NodeBoolMap::iterator it = d_testClique.begin(); it != d_testClique.end(); ++it ){
            if( (*it).second ){
              if( !isDisequal( (*it).first, newClique[j], 1 ) ){
                d_splits[ NodeManager::currentNM()->mkNode( EQUAL, (*it).first, newClique[j] ) ] = true;
                d_splitsSize = d_splitsSize + 1;
              }
            }
          }
        }
        //add new clique members to test clique
        for( int j=0; j<(int)newClique.size(); j++ ){
          d_testClique[ newClique[j] ] = true;
          d_testCliqueSize = d_testCliqueSize + 1;
        }
      }
      //check if test clique has larger size than cardinality, and forms a clique
      if( d_testCliqueSize>=long(cardinality+1) && d_splitsSize==0 ){
        //test clique is a clique
        for( NodeBoolMap::iterator it = d_testClique.begin(); it != d_testClique.end(); ++it ){
          if( (*it).second ){
            clique.push_back( (*it).first );
          }
        }
        return true;
      }
    }
  }
  return false;
}

bool StrongSolverTheoryUF::SortModel::Region::getCandidateClique( int cardinality, std::vector< Node >& clique ) {
  if( d_testCliqueSize>=long(cardinality+1) ){
    //test clique is a clique
    for( NodeBoolMap::iterator it = d_testClique.begin(); it != d_testClique.end(); ++it ){
      if( (*it).second ){
        clique.push_back( (*it).first );
      }
    }
    return true;
  }
  return false;
}

void StrongSolverTheoryUF::SortModel::Region::getNumExternalDisequalities( std::map< Node, int >& num_ext_disequalities ){
  for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
    RegionNodeInfo* rni = it->second;
    if( rni->d_valid ){
      RegionNodeInfo::DiseqList* del = rni->d_disequalities[0];
      for( NodeBoolMap::iterator it2 = del->d_disequalities.begin(); it2 != del->d_disequalities.end(); ++it2 ){
        if( (*it2).second ){
          num_ext_disequalities[ (*it2).first ]++;
        }
      }
    }
  }
}

void StrongSolverTheoryUF::SortModel::Region::debugPrint( const char* c, bool incClique ){
  Debug( c ) << "Num reps: " << d_reps_size << std::endl;
  for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
    RegionNodeInfo* rni = it->second;
    if( rni->d_valid ){
      Node n = it->first;
      Debug( c ) << "   " << n << std::endl;
      for( int i=0; i<2; i++ ){
        Debug( c ) << "      " << ( i==0 ? "Ext" : "Int" ) << " disequal:";
        RegionNodeInfo::DiseqList* del = rni->d_disequalities[i];
        for( NodeBoolMap::iterator it2 = del->d_disequalities.begin(); it2 != del->d_disequalities.end(); ++it2 ){
          if( (*it2).second ){
            Debug( c ) << " " << (*it2).first;
          }
        }
        Debug( c ) << ", total = " << del->d_size << std::endl;
      }
    }
  }
  Debug( c ) << "Total disequal: " << d_total_diseq_external << " external," << std::endl;
  Debug( c ) << "                " << d_total_diseq_internal<< " internal." << std::endl;

  if( incClique ){
    Debug( c ) << "Candidate clique members: " << std::endl;
    Debug( c ) << "   ";
    for( NodeBoolMap::iterator it = d_testClique.begin(); it != d_testClique.end(); ++ it ){
      if( (*it).second ){
        Debug( c ) << (*it).first << " ";
      }
    }
    Debug( c ) << ", size = " << d_testCliqueSize << std::endl;
    Debug( c ) << "Required splits: " << std::endl;
    Debug( c ) << "   ";
    for( NodeBoolMap::iterator it = d_splits.begin(); it != d_splits.end(); ++ it ){
      if( (*it).second ){
        Debug( c ) << (*it).first << " ";
      }
    }
    Debug( c ) << ", size = " << d_splitsSize << std::endl;
  }
}








StrongSolverTheoryUF::SortModel::SortModel( Node n, context::Context* c, context::UserContext* u, StrongSolverTheoryUF* thss ) : d_type( n.getType() ),
          d_thss( thss ), d_regions_index( c, 0 ), d_regions_map( c ), d_split_score( c ), d_disequalities_index( c, 0 ),
          d_reps( c, 0 ), d_conflict( c, false ), d_cardinality( c, 1 ), d_aloc_cardinality( u, 0 ),
          d_cardinality_assertions( c ), d_hasCard( c, false ), d_maxNegCard( c, 0 ){
  d_cardinality_term = n;
  //if( d_type.isSort() ){
  //  TypeEnumerator te(tn);
  //  d_cardinality_term = *te;
  //}else{
  //  d_cardinality_term = tn.mkGroundTerm();
  //}
}

/** initialize */
void StrongSolverTheoryUF::SortModel::initialize( OutputChannel* out ){
  allocateCardinality( out );
}

/** new node */
void StrongSolverTheoryUF::SortModel::newEqClass( Node n ){
  if( !d_conflict ){
    if( d_regions_map.find( n )==d_regions_map.end() ){
      //must generate totality axioms for every cardinality we have allocated thus far
      for( std::map< int, Node >::iterator it = d_cardinality_literal.begin(); it != d_cardinality_literal.end(); ++it ){
        if( applyTotality( it->first ) ){
          addTotalityAxiom( n, it->first, &d_thss->getOutputChannel() );
        }
      }
      if( options::ufssTotality() ){
        //regions map will store whether we need to equate this term with a constant equivalence class
        if( std::find( d_totality_terms[0].begin(), d_totality_terms[0].end(), n )==d_totality_terms[0].end() ){
          d_regions_map[n] = 0;
        }else{
          d_regions_map[n] = -1;
        }
      }else{
        if( !options::ufssRegions() ){
          //if not using regions, always add new equivalence classes to region index = 0
          d_regions_index = 0;
        }
        d_regions_map[n] = d_regions_index;
        Debug("uf-ss") << "StrongSolverTheoryUF: New Eq Class " << n << std::endl;
        Debug("uf-ss-debug") << d_regions_index << " " << (int)d_regions.size() << std::endl;
        if( d_regions_index<d_regions.size() ){
          d_regions[ d_regions_index ]->debugPrint("uf-ss-debug",true);
          d_regions[ d_regions_index ]->d_valid = true;
          Assert( !options::ufssRegions() || d_regions[ d_regions_index ]->getNumReps()==0 );
        }else{
          d_regions.push_back( new Region( this, d_thss->getSatContext() ) );
        }
        d_regions[ d_regions_index ]->addRep( n );
        d_regions_index = d_regions_index + 1;
      }
      d_reps = d_reps + 1;
    }
  }
}

/** merge */
void StrongSolverTheoryUF::SortModel::merge( Node a, Node b ){
  if( !d_conflict ){
    if( options::ufssTotality() ){
      if( d_regions_map[b]==-1 ){
        d_regions_map[a] = -1;
      }
      d_regions_map[b] = -1;
    }else{
      //Assert( a==d_th->d_equalityEngine.getRepresentative( a ) );
      //Assert( b==d_th->d_equalityEngine.getRepresentative( b ) );
      Debug("uf-ss") << "StrongSolverTheoryUF: Merging " << a << " = " << b << "..." << std::endl;
      if( a!=b ){
        Assert( d_regions_map.find( a )!=d_regions_map.end() );
        Assert( d_regions_map.find( b )!=d_regions_map.end() );
        int ai = d_regions_map[a];
        int bi = d_regions_map[b];
        Debug("uf-ss") << "   regions: " << ai << " " << bi << std::endl;
        if( ai!=bi ){
          if( d_regions[ai]->getNumReps()==1  ){
            int ri = combineRegions( bi, ai );
            d_regions[ri]->setEqual( a, b );
            checkRegion( ri );
          }else if( d_regions[bi]->getNumReps()==1 ){
            int ri = combineRegions( ai, bi );
            d_regions[ri]->setEqual( a, b );
            checkRegion( ri );
          }else{
            // either move a to d_regions[bi], or b to d_regions[ai]
            int aex = d_regions[ai]->d_nodes[a]->getNumInternalDisequalities() - getNumDisequalitiesToRegion( a, bi );
            int bex = d_regions[bi]->d_nodes[b]->getNumInternalDisequalities() - getNumDisequalitiesToRegion( b, ai );
            //based on which would produce the fewest number of external disequalities
            if( aex<bex ){
              moveNode( a, bi );
              d_regions[bi]->setEqual( a, b );
            }else{
              moveNode( b, ai );
              d_regions[ai]->setEqual( a, b );
            }
            checkRegion( ai );
            checkRegion( bi );
          }
        }else{
          d_regions[ai]->setEqual( a, b );
          checkRegion( ai );
        }
        d_regions_map[b] = -1;
      }
      d_reps = d_reps - 1;

      if( !d_conflict ){
        if( options::ufssDiseqPropagation() ){
          //notify the disequality propagator
          d_thss->getDisequalityPropagator()->merge(a, b);
        }
        if( options::ufssSymBreak() ){
          d_thss->getSymmetryBreaker()->merge(a, b);
        }
      }
    }
  }
}

/** assert terms are disequal */
void StrongSolverTheoryUF::SortModel::assertDisequal( Node a, Node b, Node reason ){
  if( !d_conflict ){
    if( options::ufssTotality() ){
      //do nothing
    }else{
      //if they are not already disequal
      a = d_thss->getTheory()->d_equalityEngine.getRepresentative( a );
      b = d_thss->getTheory()->d_equalityEngine.getRepresentative( b );
      int ai = d_regions_map[a];
      int bi = d_regions_map[b];
      if( !d_regions[ai]->isDisequal( a, b, ai==bi ) ){
        Debug("uf-ss") << "Assert disequal " << a << " != " << b << "..." << std::endl;
        //if( reason.getKind()!=NOT || ( reason[0].getKind()!=EQUAL && reason[0].getKind()!=IFF ) ||
        //    a!=reason[0][0] || b!=reason[0][1] ){
        //  Notice() << "Assert disequal " << a << " != " << b << ", reason = " << reason << "..." << std::endl;
        //}
        Debug("uf-ss-disequal") << "Assert disequal " << a << " != " << b << "..." << std::endl;
        //add to list of disequalities
        if( d_disequalities_index<d_disequalities.size() ){
          d_disequalities[d_disequalities_index] = reason;
        }else{
          d_disequalities.push_back( reason );
        }
        d_disequalities_index = d_disequalities_index + 1;
        //now, add disequalities to regions
        Assert( d_regions_map.find( a )!=d_regions_map.end() );
        Assert( d_regions_map.find( b )!=d_regions_map.end() );
        Debug("uf-ss") << "   regions: " << ai << " " << bi << std::endl;
        if( ai==bi ){
          //internal disequality
          d_regions[ai]->setDisequal( a, b, 1, true );
          d_regions[ai]->setDisequal( b, a, 1, true );
          checkRegion( ai, false );  //do not need to check if it needs to combine (no new ext. disequalities)
        }else{
          //external disequality
          d_regions[ai]->setDisequal( a, b, 0, true );
          d_regions[bi]->setDisequal( b, a, 0, true );
          checkRegion( ai );
          checkRegion( bi );
        }

        if( !d_conflict ){
          if( options::ufssDiseqPropagation() ){
            //notify the disequality propagator
            d_thss->getDisequalityPropagator()->assertDisequal(a, b, Node::null());
          }
          if( options::ufssSymBreak() ){
            d_thss->getSymmetryBreaker()->assertDisequal(a, b);
          }
        }
      }
    }
  }
}

bool StrongSolverTheoryUF::SortModel::areDisequal( Node a, Node b ) {
  Assert( a == d_thss->getTheory()->d_equalityEngine.getRepresentative( a ) );
  Assert( b == d_thss->getTheory()->d_equalityEngine.getRepresentative( b ) );
  if( d_regions_map.find( a )!=d_regions_map.end() &&
      d_regions_map.find( b )!=d_regions_map.end() ){
    int ai = d_regions_map[a];
    int bi = d_regions_map[b];
    return d_regions[ai]->isDisequal(a, b, ai==bi ? 1 : 0);
  }else{
    return false;
  }
}

/** check */
void StrongSolverTheoryUF::SortModel::check( Theory::Effort level, OutputChannel* out ){
  if( level>=Theory::EFFORT_STANDARD && d_hasCard && !d_conflict ){
    Debug("uf-ss") << "StrongSolverTheoryUF: Check " << level << " " << d_type << std::endl;
    //Notice() << "StrongSolverTheoryUF: Check " << level << std::endl;
    if( d_reps<=(unsigned)d_cardinality ){
      Debug("uf-ss-debug") << "We have " << d_reps << " representatives for type " << d_type << ", <= " << d_cardinality << std::endl;
      if( level==Theory::EFFORT_FULL ){
        Debug("uf-ss-sat") << "We have " << d_reps << " representatives for type " << d_type << ", <= " << d_cardinality << std::endl;
        //Notice() << "We have " << d_reps << " representatives for type " << d_type << ", <= " << cardinality << std::endl;
        //Notice() << "Model size for " << d_type << " is " << cardinality << std::endl;
        //Notice() << cardinality << " ";
      }
      return;
    }else{
      //first check if we can generate a clique conflict
      if( !options::ufssTotality() ){
        //do a check within each region
        for( int i=0; i<(int)d_regions_index; i++ ){
          if( d_regions[i]->d_valid ){
            std::vector< Node > clique;
            if( d_regions[i]->check( level, d_cardinality, clique ) ){
              if( options::ufssMode()==UF_SS_FULL ){
                //add clique lemma
                addCliqueLemma( clique, out );
                return;
              }
            }else{
              Trace("uf-ss-debug") << "No clique in Region #" << i << std::endl;
            }
          }
        }
      }
      if( !applyTotality( d_cardinality ) ){
        //do splitting on demand
        bool addedLemma = false;
        if( level==Theory::EFFORT_FULL || options::ufssEagerSplits() ){
          Trace("uf-ss-debug") << "Add splits?" << std::endl;
          //see if we have any recommended splits from large regions
          for( int i=0; i<(int)d_regions_index; i++ ){
            if( d_regions[i]->d_valid && d_regions[i]->getNumReps()>d_cardinality ){
              //just add the clique lemma
              if( level==Theory::EFFORT_FULL && options::ufssCliqueSplits() ){
                std::vector< Node > clique;
                if( d_regions[i]->getCandidateClique( d_cardinality, clique ) ){
                  //add clique lemma
                  addCliqueLemma( clique, out );
                  return;
                }
              }else{
                int sp = addSplit( d_regions[i], out );
                if( sp==1 ){
                  addedLemma = true;
#ifdef ONE_SPLIT_REGION
                  break;
#endif
                }else if( sp==-1 ){
                  check( level, out );
                  return;
                }
              }
            }
          }
        }
        //if no added lemmas, force continuation via combination of regions
        if( level==Theory::EFFORT_FULL ){
          if( !addedLemma ){
            Trace("uf-ss-debug") << "No splits added. " << d_cardinality << std::endl;
            Trace("uf-ss-si")  << "Must combine region" << std::endl;
            bool recheck = false;
            if( options::sortInference()){
              //if sort inference is enabled, search for regions with same sort
              std::map< int, int > sortsFound;
              for( int i=0; i<(int)d_regions_index; i++ ){
                if( d_regions[i]->d_valid ){
                  Node op = d_regions[i]->d_nodes.begin()->first;
                  int sort_id = d_thss->getSortInference()->getSortId(op);
                  if( sortsFound.find( sort_id )!=sortsFound.end() ){
                    combineRegions( sortsFound[sort_id], i );
                    recheck = true;
                    break;
                  }else{
                    sortsFound[sort_id] = i;
                  }
                }
              }
            }
            if( !recheck ) {
              //naive strategy, force region combination involving the first valid region
              for( int i=0; i<(int)d_regions_index; i++ ){
                if( d_regions[i]->d_valid ){
                  int fcr = forceCombineRegion( i, false );
                  Trace("uf-ss-debug") << "Combined regions " << i << " " << fcr << std::endl;
                  if( options::ufssMode()==UF_SS_FULL || fcr!=-1 ){
                    recheck = true;
                    break;
                  }
                }
              }
            }
            if( recheck ){
              Trace("uf-ss-debug") << "Must recheck." << std::endl;
              check( level, out );
            }
          }
        }
      }
    }
  }
}

void StrongSolverTheoryUF::SortModel::propagate( Theory::Effort level, OutputChannel* out ){

}

Node StrongSolverTheoryUF::SortModel::getNextDecisionRequest(){
  //request the current cardinality as a decision literal, if not already asserted
  for( int i=1; i<=d_aloc_cardinality; i++ ){
    if( !d_hasCard || i<d_cardinality ){
      Node cn = d_cardinality_literal[ i ];
      Assert( !cn.isNull() );
      if( d_cardinality_assertions.find( cn )==d_cardinality_assertions.end() ){
        Trace("uf-ss-dec") << "Propagate as decision " << d_type << " " << i << std::endl;
        return cn;
      }
    }
  }
  return Node::null();
}

bool StrongSolverTheoryUF::SortModel::minimize( OutputChannel* out, TheoryModel* m ){
  if( options::ufssTotality() ){
    //do nothing
  }else{
    if( m ){
#if 0
      // ensure that the constructed model is minimal
      // if the model has terms that the strong solver does not know about
      if( (int)m->d_rep_set.d_type_reps[ d_type ].size()>d_cardinality ){
        eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &m->d_equalityEngine );
        while( !eqcs_i.isFinished() ){
          Node eqc = (*eqcs_i);
          if( eqc.getType()==d_type ){
            //we must ensure that this equivalence class has been accounted for
            if( d_regions_map.find( eqc )==d_regions_map.end() ){
              //split on unaccounted for term and cardinality lemma term (as default)
              Node splitEq = eqc.eqNode( d_cardinality_term );
              splitEq = Rewriter::rewrite( splitEq );
              Trace("uf-ss-minimize") << "Last chance minimize : " << splitEq << std::endl;
              out->split( splitEq );
              //tell the sat solver to explore the equals branch first
              out->requirePhase( splitEq, true );
              ++( d_thss->d_statistics.d_split_lemmas );
              return false;
            }
          }
          ++eqcs_i;
        }
        Assert( false );
      }
#endif
    }else{
      Trace("uf-ss-debug")  << "Minimize the UF model..." << std::endl;
      //internal minimize, ensure that model forms a clique:
      // if two equivalence classes are neither equal nor disequal, add a split
      int validRegionIndex = -1;
      for( int i=0; i<(int)d_regions_index; i++ ){
        if( d_regions[i]->d_valid ){
          if( validRegionIndex!=-1 ){
            combineRegions( validRegionIndex, i );
            if( addSplit( d_regions[validRegionIndex], out )!=0 ){
              Trace("uf-ss-debug") << "Minimize model : combined regions, found split. " << std::endl;
              return false;
            }
          }else{
            validRegionIndex = i;
          }
        }
      }
      Assert( validRegionIndex!=-1 );
      if( addSplit( d_regions[validRegionIndex], out )!=0 ){
        Trace("uf-ss-debug") << "Minimize model : found split. " << std::endl;
        return false;
      }
      Trace("uf-ss-debug") << "Minimize success. " << std::endl;
    }
  }
  return true;
}


int StrongSolverTheoryUF::SortModel::getNumDisequalitiesToRegion( Node n, int ri ){
  int ni = d_regions_map[n];
  int counter = 0;
  Region::RegionNodeInfo::DiseqList* del = d_regions[ni]->d_nodes[n]->d_disequalities[0];
  for( NodeBoolMap::iterator it = del->d_disequalities.begin(); it != del->d_disequalities.end(); ++it ){
    if( (*it).second ){
      if( d_regions_map[ (*it).first ]==ri ){
        counter++;
      }
    }
  }
  return counter;
}

void StrongSolverTheoryUF::SortModel::getDisequalitiesToRegions( int ri, std::map< int, int >& regions_diseq ){
  for( std::map< Node, Region::RegionNodeInfo* >::iterator it = d_regions[ri]->d_nodes.begin();
       it != d_regions[ri]->d_nodes.end(); ++it ){
    if( it->second->d_valid ){
      Region::RegionNodeInfo::DiseqList* del = it->second->d_disequalities[0];
      for( NodeBoolMap::iterator it2 = del->d_disequalities.begin(); it2 != del->d_disequalities.end(); ++it2 ){
        if( (*it2).second ){
          Assert( isValid( d_regions_map[ (*it2).first ] ) );
          //Notice() << "Found disequality with " << (*it2).first << ", region = " << d_regions_map[ (*it2).first ] << std::endl;
          regions_diseq[ d_regions_map[ (*it2).first ] ]++;
        }
      }
    }
  }
}

void StrongSolverTheoryUF::SortModel::setSplitScore( Node n, int s ){
  if( d_split_score.find( n )!=d_split_score.end() ){
    int ss = d_split_score[ n ];
    d_split_score[ n ] = s>ss ? s : ss;
  }else{
    d_split_score[ n ] = s;
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    setSplitScore( n[i], s+1 );
  }
}

void StrongSolverTheoryUF::SortModel::assertCardinality( OutputChannel* out, int c, bool val ){
  if( !d_conflict ){
    Trace("uf-ss-assert") << "Assert cardinality " << d_type << " " << c << " " << val << " level = ";
    Trace("uf-ss-assert") << d_thss->getTheory()->d_valuation.getAssertionLevel() << std::endl;
    Node cl = getCardinalityLiteral( c );
    d_cardinality_assertions[ cl ] = val;
    if( val ){
      bool doCheckRegions = !d_hasCard;
      bool prevHasCard = d_hasCard;
      d_hasCard = true;
      if( !prevHasCard || c<d_cardinality ){
        d_cardinality = c;
        simpleCheckCardinality();
        if( d_thss->d_conflict.get() ){
          return;
        }
      }
      //should check all regions now
      if( doCheckRegions ){
        for( int i=0; i<(int)d_regions_index; i++ ){
          if( d_regions[i]->d_valid ){
            checkRegion( i );
            if( d_conflict ){
              return;
            }
          }
        }
      }
    }else{
      /*
      if( options::ufssModelInference() ){
        //check if we are at decision level 0
        if( d_th->d_valuation.getAssertionLevel()==0 ){
          Trace("uf-ss-mi") << "We have proved that no models of size " << c << " for type " << d_type << " exist." << std::endl;
          Trace("uf-ss-mi") << "  # Clique lemmas : " << d_cliques[c].size() << std::endl;
          if( d_cliques[c].size()==1 ){
            if( d_totality_terms[c+1].empty() ){
              Trace("uf-ss-mi") << "*** Establish model" << std::endl;
              //d_totality_terms[c+1].insert( d_totality_terms[c].begin(), d_cliques[c][0].begin(), d_cliques[c][0].end() );
            }
          }
        }
      }
      */
      //see if we need to request a new cardinality
      if( !d_hasCard ){
        bool needsCard = true;
        for( std::map< int, Node >::iterator it = d_cardinality_literal.begin(); it!=d_cardinality_literal.end(); ++it ){
          if( d_cardinality_assertions.find( it->second )==d_cardinality_assertions.end() ){
            Debug("fmf-card-debug") << "..does not need allocate because of " << it->second << std::endl;
            needsCard = false;
            break;
          }
        }
        if( needsCard ){
          allocateCardinality( out );
        }
      }else{
        Debug("fmf-card-debug") << "..already has card = " << d_cardinality << std::endl;
      }
      if( c>d_maxNegCard.get() ){
        Trace("uf-ss-com-card-debug") << "Maximum negative cardinality for " << d_type << " is now " << c << std::endl;
        d_maxNegCard.set( c );
        simpleCheckCardinality();
      }
    }
  }
}

void StrongSolverTheoryUF::SortModel::checkRegion( int ri, bool checkCombine ){
  if( isValid(ri) && d_hasCard ){
    Assert( d_cardinality>0 );
    if( checkCombine && d_regions[ri]->getMustCombine( d_cardinality ) ){
      ////alternatively, check if we can reduce the number of external disequalities by moving single nodes
      //for( std::map< Node, bool >::iterator it = d_regions[i]->d_reps.begin(); it != d_regions[i]->d_reps.end(); ++it ){
      //  if( it->second ){
      //    int inDeg = d_regions[i]->d_disequalities_size[1][ it-> first ];
      //    int outDeg = d_regions[i]->d_disequalities_size[0][ it-> first ];
      //    if( inDeg<outDeg ){
      //    }
      //  }
      //}
      int riNew = forceCombineRegion( ri, true );
      if( riNew>=0 ){
        checkRegion( riNew, checkCombine );
      }
    }
    //now check if region is in conflict
    std::vector< Node > clique;
    if( d_regions[ri]->check( Theory::EFFORT_STANDARD, d_cardinality, clique ) ){
      if( options::ufssMode()==UF_SS_FULL ){
        //explain clique
        addCliqueLemma( clique, &d_thss->getOutputChannel() );
      }
    }
  }
}

int StrongSolverTheoryUF::SortModel::forceCombineRegion( int ri, bool useDensity ){
  if( !useDensity ){
    for( int i=0; i<(int)d_regions_index; i++ ){
      if( ri!=i && d_regions[i]->d_valid ){
        return combineRegions( ri, i );
      }
    }
    return -1;
  }else{
    //this region must merge with another
    Debug("uf-ss-check-region") << "We must combine Region #" << ri << ". " << std::endl;
    d_regions[ri]->debugPrint("uf-ss-check-region");
    //take region with maximum disequality density
    double maxScore = 0;
    int maxRegion = -1;
    std::map< int, int > regions_diseq;
    getDisequalitiesToRegions( ri, regions_diseq );
    for( std::map< int, int >::iterator it = regions_diseq.begin(); it != regions_diseq.end(); ++it ){
      Debug("uf-ss-check-region") << it->first << " : " << it->second << std::endl;
    }
    for( std::map< int, int >::iterator it = regions_diseq.begin(); it != regions_diseq.end(); ++it ){
      Assert( it->first!=ri );
      Assert( isValid( it->first ) );
      Assert( d_regions[ it->first ]->getNumReps()>0 );
      double tempScore = double(it->second)/double(d_regions[it->first]->getNumReps() );
      if( tempScore>maxScore ){
        maxRegion = it->first;
        maxScore = tempScore;
      }
    }
    if( maxRegion!=-1 ){
      Debug("uf-ss-check-region") << "Combine with region #" << maxRegion << ":" << std::endl;
      d_regions[maxRegion]->debugPrint("uf-ss-check-region");
      return combineRegions( ri, maxRegion );
    }
    return -1;
  }
}


int StrongSolverTheoryUF::SortModel::combineRegions( int ai, int bi ){
#ifdef COMBINE_REGIONS_SMALL_INTO_LARGE
  if( d_regions[ai]->getNumReps()<d_regions[bi]->getNumReps() ){
    return combineRegions( bi, ai );
  }
#endif
  Debug("uf-ss-region") << "uf-ss: Combine Region #" << bi << " with Region #" << ai << std::endl;
  Assert( isValid( ai ) && isValid( bi ) );
  for( std::map< Node, Region::RegionNodeInfo* >::iterator it = d_regions[bi]->d_nodes.begin(); it != d_regions[bi]->d_nodes.end(); ++it ){
    Region::RegionNodeInfo* rni = it->second;
    if( rni->d_valid ){
      d_regions_map[ it->first ] = ai;
    }
  }
  //update regions disequal DO_THIS?
  d_regions[ai]->combine( d_regions[bi] );
  d_regions[bi]->d_valid = false;
  return ai;
}

void StrongSolverTheoryUF::SortModel::moveNode( Node n, int ri ){
  Debug("uf-ss-region") << "uf-ss: Move node " << n << " to Region #" << ri << std::endl;
  Assert( isValid( d_regions_map[ n ] ) );
  Assert( isValid( ri ) );
  //move node to region ri
  d_regions[ri]->takeNode( d_regions[ d_regions_map[n] ], n );
  d_regions_map[n] = ri;
}

void StrongSolverTheoryUF::SortModel::allocateCardinality( OutputChannel* out ){
  if( d_aloc_cardinality>0 ){
    Trace("uf-ss-fmf") << "No model of size " << d_aloc_cardinality << " exists for type " << d_type << " in this branch" << std::endl;
  }
  if( Trace.isOn("uf-ss-cliques") ){
    Trace("uf-ss-cliques") << "Cliques of size " << (d_aloc_cardinality+1) << " for " << d_type << " : " << std::endl;
    for( size_t i=0; i<d_cliques[ d_aloc_cardinality ].size(); i++ ){
      Trace("uf-ss-cliques") << "  ";
      for( size_t j=0; j<d_cliques[ d_aloc_cardinality ][i].size(); j++ ){
        Trace("uf-ss-cliques") << d_cliques[ d_aloc_cardinality ][i][j] << " ";
      }
      Trace("uf-ss-cliques") << std::endl;
    }
  }

  //allocate the lowest such that it is not asserted
  Node cl;
  do {
    d_aloc_cardinality = d_aloc_cardinality + 1;
    cl = getCardinalityLiteral( d_aloc_cardinality );
  }while( d_cardinality_assertions.find( cl )!=d_cardinality_assertions.end() && !d_cardinality_assertions[cl] );
  //if one is already asserted postively, abort
  if( d_cardinality_assertions.find( cl )!=d_cardinality_assertions.end() ){
    return;
  }

  //check for abort case
  if( options::ufssAbortCardinality()==d_aloc_cardinality ){
    //abort here DO_THIS
    Message() << "Maximum cardinality reached." << std::endl;
    exit( 0 );
  }else{
    if( applyTotality( d_aloc_cardinality ) ){
      //must generate new cardinality lemma term
      Node var;
      if( d_aloc_cardinality==1 && !options::ufssTotalitySymBreak() ){
        //get arbitrary ground term
        var = d_cardinality_term;
      }else{
        std::stringstream ss;
        ss << "_c_" << d_aloc_cardinality;
        var = NodeManager::currentNM()->mkSkolem( ss.str(), d_type, "is a cardinality lemma term" );
      }
      d_totality_terms[0].push_back( var );
      Trace("mkVar") << "allocateCardinality, mkVar : " << var << " : " << d_type << std::endl;
      //must be distinct from all other cardinality terms
      for( int i=0; i<(int)(d_totality_terms[0].size()-1); i++ ){
        Node lem = NodeManager::currentNM()->mkNode( NOT, var.eqNode( d_totality_terms[0][i] ) );
        d_thss->getOutputChannel().lemma( lem );
      }
    }

    //add splitting lemma for cardinality constraint
    Assert( !d_cardinality_term.isNull() );
    Node lem = getCardinalityLiteral( d_aloc_cardinality );
    lem = NodeManager::currentNM()->mkNode( OR, lem, lem.notNode() );
    d_cardinality_lemma[ d_aloc_cardinality ] = lem;
    //add as lemma to output channel
    out->lemma( lem );
    //require phase
    out->requirePhase( d_cardinality_literal[ d_aloc_cardinality ], true );
    //add the appropriate lemma, propagate as decision
    //Trace("uf-ss-prop-as-dec") << "Propagate as decision " << lem[0] << " " << d_type << std::endl;
    //out->propagateAsDecision( lem[0] );
    d_thss->d_statistics.d_max_model_size.maxAssign( d_aloc_cardinality );

    if( applyTotality( d_aloc_cardinality ) ){
      //must send totality axioms for each existing term
      for( NodeIntMap::iterator it = d_regions_map.begin(); it != d_regions_map.end(); ++it ){
        addTotalityAxiom( (*it).first, d_aloc_cardinality, &d_thss->getOutputChannel() );
      }
    }
  }
}

int StrongSolverTheoryUF::SortModel::addSplit( Region* r, OutputChannel* out ){
  Node s;
  if( r->hasSplits() ){
    //take the first split you find
    for( NodeBoolMap::iterator it = r->d_splits.begin(); it != r->d_splits.end(); ++it ){
      if( (*it).second ){
        s = (*it).first;
        break;
      }
    }
    Assert( s!=Node::null() );
  }else{
    if( options::ufssMode()!=UF_SS_FULL ){
      //since candidate clique is not reported, we may need to find splits manually
      for ( std::map< Node, Region::RegionNodeInfo* >::iterator it = r->d_nodes.begin(); it != r->d_nodes.end(); ++it ){
        if ( it->second->d_valid ){
          for ( std::map< Node, Region::RegionNodeInfo* >::iterator it2 = r->d_nodes.begin(); it2 != r->d_nodes.end(); ++it2 ){
            if ( it->second!=it2->second && it2->second->d_valid ){
              if( !r->isDisequal( it->first, it2->first, 1 ) ){
                s = NodeManager::currentNM()->mkNode( EQUAL, it->first, it2->first );
              }
            }
          }
        }
      }
    }
  }
  if (!s.isNull() ){
    //add lemma to output channel
    Assert( s.getKind()==EQUAL );
    Trace("uf-ss-lemma") << "*** Split on " << s << std::endl;
    Node ss = Rewriter::rewrite( s );
    if( ss.getKind()!=EQUAL ){
      Node b_t = NodeManager::currentNM()->mkConst( true );
      Node b_f = NodeManager::currentNM()->mkConst( false );
      if( ss==b_f ){
        Trace("uf-ss-lemma") << "....Assert disequal directly : " << s[0] << " " << s[1] << std::endl;
        assertDisequal( s[0], s[1], b_t );
        return -1;
      }else{
        Trace("uf-ss-warn") << "Split on unknown literal : " << ss << std::endl;
      }
      if( ss==b_t ){
        Message() << "Bad split " << s << std::endl;
        exit( 16 );
      }
    }
    if( options::sortInference()) {
      for( int i=0; i<2; i++ ){
        int si = d_thss->getSortInference()->getSortId( ss[i] );
        Trace("uf-ss-split-si") << si << " ";
      }
      Trace("uf-ss-split-si")  << std::endl;
    }
    //Trace("uf-ss-lemma") << d_th->getEqualityEngine()->areEqual( s[0], s[1] ) << " ";
    //Trace("uf-ss-lemma") << d_th->getEqualityEngine()->areDisequal( s[0], s[1] ) << std::endl;
    //Trace("uf-ss-lemma") << s[0].getType() << " " << s[1].getType() << std::endl;
    //Notice() << "*** Split on " << s << std::endl;
    //split on the equality s
    out->split( ss );
    //tell the sat solver to explore the equals branch first
    out->requirePhase( ss, true );
    ++( d_thss->d_statistics.d_split_lemmas );
    return 1;
  }else{
    return 0;
  }
}


void StrongSolverTheoryUF::SortModel::addCliqueLemma( std::vector< Node >& clique, OutputChannel* out ){
  Assert( d_hasCard );
  Assert( d_cardinality>0 );
  while( clique.size()>size_t(d_cardinality+1) ){
    clique.pop_back();
  }
  //debugging information
  if( Trace.isOn("uf-ss-cliques") ){
    std::vector< Node > clique_vec;
    clique_vec.insert( clique_vec.begin(), clique.begin(), clique.end() );
    addClique( d_cardinality, clique_vec );
  }
  if( options::ufssSimpleCliques() && !options::ufssExplainedCliques() ){
    //add as lemma
    std::vector< Node > eqs;
    for( int i=0; i<(int)clique.size(); i++ ){
      for( int j=0; j<i; j++ ){
        Node r1 = d_thss->getTheory()->d_equalityEngine.getRepresentative(clique[i]);
        Node r2 = d_thss->getTheory()->d_equalityEngine.getRepresentative(clique[j]);
        eqs.push_back( clique[i].eqNode( clique[j] ) );
      }
    }
    eqs.push_back( d_cardinality_literal[ d_cardinality ].notNode() );
    Node lem = NodeManager::currentNM()->mkNode( OR, eqs );
    Trace("uf-ss-lemma") << "*** Add clique lemma " << lem << std::endl;
    ++( d_thss->d_statistics.d_clique_lemmas );
    out->lemma( lem );
  }else{
    //found a clique
    Debug("uf-ss-cliques") << "Found a clique (cardinality=" << d_cardinality << ") :" << std::endl;
    Debug("uf-ss-cliques") << "   ";
    for( int i=0; i<(int)clique.size(); i++ ){
      Debug("uf-ss-cliques") << clique[i] << " ";
    }
    Debug("uf-ss-cliques") << std::endl;
    Debug("uf-ss-cliques") << "Finding clique disequalities..." << std::endl;

    //we will scan through each of the disequaltities
    bool isSatConflict = true;
    std::vector< Node > conflict;
    //collect disequalities, and nodes that must be equal within representatives
    std::map< Node, std::map< Node, bool > > explained;
    std::map< Node, std::map< Node, bool > > nodesWithinRep;
    //map from the reprorted clique members to those reported in the lemma
    std::map< Node, Node > cliqueRepMap;
    for( int i=0; i<(int)d_disequalities_index; i++ ){
      //if both sides of disequality exist in clique
      Node r1 = d_thss->getTheory()->d_equalityEngine.getRepresentative( d_disequalities[i][0][0] );
      Node r2 = d_thss->getTheory()->d_equalityEngine.getRepresentative( d_disequalities[i][0][1] );
      if( r1!=r2 && ( explained.find( r1 )==explained.end() || explained[r1].find( r2 )==explained[r1].end() ) &&
          std::find( clique.begin(), clique.end(), r1 )!=clique.end() &&
          std::find( clique.begin(), clique.end(), r2 )!=clique.end() ){
        explained[r1][r2] = true;
        explained[r2][r1] = true;
        if( options::ufssExplainedCliques() ){
          conflict.push_back( d_disequalities[i] );
          Debug("uf-ss-cliques") << "   -> disequality : " << d_disequalities[i] << std::endl;
          nodesWithinRep[r1][ d_disequalities[i][0][0] ] = true;
          nodesWithinRep[r2][ d_disequalities[i][0][1] ] = true;
        }else{
          //get the terms we report in the lemma
          Node ru1 = r1;
          if( cliqueRepMap.find( r1 )==cliqueRepMap.end() ){
            ru1 = d_disequalities[i][0][0];
            cliqueRepMap[r1] = ru1;
          }else{
            ru1 = cliqueRepMap[r1];
          }
          Node ru2 = r2;
          if( cliqueRepMap.find( r2 )==cliqueRepMap.end() ){
            ru2 = d_disequalities[i][0][1];
            cliqueRepMap[r2] = ru2;
          }else{
            ru2 = cliqueRepMap[r2];
          }
          if( ru1!=d_disequalities[i][0][0] || ru2!=d_disequalities[i][0][1] ){
            //disequalities have endpoints that are not connected within an equivalence class
            // we will be producing a lemma, introducing a new literal ru1 != ru2
            conflict.push_back( ru1.eqNode( ru2 ).notNode() );
            isSatConflict = false;
          }else{
            conflict.push_back( d_disequalities[i] );
          }
        }
        if( conflict.size()==(clique.size()*( clique.size()-1 )/2) ){
          break;
        }
      }
    }
    if( options::ufssExplainedCliques() ){
      //Debug("uf-ss-cliques") << conflict.size() << " " << clique.size() << std::endl;
      Assert( (int)conflict.size()==((int)clique.size()*( (int)clique.size()-1 )/2) );
      //Assert( (int)conflict.size()==(int)clique.size()*( (int)clique.size()-1 )/2 );
      Debug("uf-ss-cliques") << "Finding clique equalities internal to eq classes..." << std::endl;
      //now, we must explain equalities within each equivalence class
      for( std::map< Node, std::map< Node, bool > >::iterator it = nodesWithinRep.begin(); it != nodesWithinRep.end(); ++it ){
        if( it->second.size()>1 ){
          Node prev;
          //add explanation of t1 = t2 = ... = tn
          Debug("uf-ss-cliques") << "Explain ";
          for( std::map< Node, bool >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
            if( prev!=Node::null() ){
              Debug("uf-ss-cliques") << " = ";
              //explain it2->first and prev
              std::vector< TNode > expl;
              d_thss->getTheory()->d_equalityEngine.explainEquality( it2->first, prev, true, expl );
              for( int i=0; i<(int)expl.size(); i++ ){
                if( std::find( conflict.begin(), conflict.end(), expl[i] )==conflict.end() ){
                  conflict.push_back( expl[i] );
                }
              }
            }
            prev = it2->first;
            Debug("uf-ss-cliques") << prev;
          }
          Debug("uf-ss-cliques") << std::endl;
        }
      }
      Debug("uf-ss-cliques") << "Explanation of clique (size=" << conflict.size() << ") = " << std::endl;
      for( int i=0; i<(int)conflict.size(); i++ ){
        Debug("uf-ss-cliques") << conflict[i] << " ";
      }
      Debug("uf-ss-cliques") << std::endl;
    }
    //now, make the conflict
    if( isSatConflict ){
      conflict.push_back( d_cardinality_literal[ d_cardinality ] );
      Node conflictNode = NodeManager::currentNM()->mkNode( AND, conflict );
      Trace("uf-ss-lemma") << "*** Add clique conflict " << conflictNode << std::endl;
      //Notice() << "*** Add clique conflict " << conflictNode << std::endl;
      out->conflict( conflictNode );
      d_conflict = true;
      ++( d_thss->d_statistics.d_clique_conflicts );
    }else{
      Node conflictNode = conflict.size()==1 ? conflict[0] : NodeManager::currentNM()->mkNode( AND, conflict );
      //add cardinality constraint
      Node cardNode = d_cardinality_literal[ d_cardinality ];
      //bool value;
      //bool hasValue = d_th->getValuation().hasSatValue( cardNode, value );
      //Assert( hasValue );
      //Assert( value );
      conflictNode = NodeManager::currentNM()->mkNode( IMPLIES, conflictNode, cardNode.notNode() );
      Trace("uf-ss-lemma") << "*** Add clique lemma " << conflictNode << std::endl;
      out->lemma( conflictNode );
      ++( d_thss->d_statistics.d_clique_lemmas );
    }

    //DO_THIS: ensure that the same clique is not reported???  Check standard effort after assertDisequal can produce same clique.
  }
}

void StrongSolverTheoryUF::SortModel::addTotalityAxiom( Node n, int cardinality, OutputChannel* out ){
  if( std::find( d_totality_terms[0].begin(), d_totality_terms[0].end(), n )==d_totality_terms[0].end() ){
    if( std::find( d_totality_lems[n].begin(), d_totality_lems[n].end(), cardinality ) == d_totality_lems[n].end() ){
      d_totality_lems[n].push_back( cardinality );
      Node cardLit = d_cardinality_literal[ cardinality ];
      int sort_id = 0;
      if( options::sortInference() ){
        sort_id = d_thss->getSortInference()->getSortId(n);
      }
      Trace("uf-ss-totality") << "Add totality lemma for " << n << " " << cardinality << ", sort id is " << sort_id << std::endl;
      int use_cardinality = cardinality;
      if( options::ufssTotalitySymBreak() ){
        if( d_sym_break_index.find(n)!=d_sym_break_index.end() ){
          use_cardinality = d_sym_break_index[n];
        }else if( (int)d_sym_break_terms[n.getType()][sort_id].size()<cardinality-1 ){
          use_cardinality = d_sym_break_terms[n.getType()][sort_id].size() + 1;
          d_sym_break_terms[n.getType()][sort_id].push_back( n );
          d_sym_break_index[n] = use_cardinality;
          Trace("uf-ss-totality") << "Allocate symmetry breaking term " << n << ", index = " << use_cardinality << std::endl;
          if( d_sym_break_terms[n.getType()][sort_id].size()>1 ){
            //enforce canonicity
            for( int i=2; i<use_cardinality; i++ ){
              //can only be assigned to domain constant d if someone has been assigned domain constant d-1
              Node eq = n.eqNode( getTotalityLemmaTerm( cardinality, i ) );
              std::vector< Node > eqs;
              for( unsigned j=0; j<(d_sym_break_terms[n.getType()][sort_id].size()-1); j++ ){
                eqs.push_back( d_sym_break_terms[n.getType()][sort_id][j].eqNode( getTotalityLemmaTerm( cardinality, i-1 ) ) );
              }
              Node ax = NodeManager::currentNM()->mkNode( OR, eqs );
              Node lem = NodeManager::currentNM()->mkNode( IMPLIES, eq, ax );
              Trace("uf-ss-lemma") << "*** Add (canonicity) totality axiom " << lem << std::endl;
              d_thss->getOutputChannel().lemma( lem );
            }
          }
        }
      }

      std::vector< Node > eqs;
      for( int i=0; i<use_cardinality; i++ ){
        eqs.push_back( n.eqNode( getTotalityLemmaTerm( cardinality, i ) ) );
      }
      Node ax = NodeManager::currentNM()->mkNode( OR, eqs );
      Node lem = NodeManager::currentNM()->mkNode( IMPLIES, cardLit, ax );
      Trace("uf-ss-lemma") << "*** Add totality axiom " << lem << std::endl;
      //send as lemma to the output channel
      d_thss->getOutputChannel().lemma( lem );
      ++( d_thss->d_statistics.d_totality_lemmas );
    }
  }
}

void StrongSolverTheoryUF::SortModel::addClique( int c, std::vector< Node >& clique ) {

  if( d_clique_trie[c].add( clique ) ){
    d_cliques[ c ].push_back( clique );
  }
}


/** apply totality */
bool StrongSolverTheoryUF::SortModel::applyTotality( int cardinality ){
  return options::ufssTotality() || cardinality<=options::ufssTotalityLimited();
  // || ( options::ufssModelInference() && !d_totality_terms[cardinality].empty() );
}

/** get totality lemma terms */
Node StrongSolverTheoryUF::SortModel::getTotalityLemmaTerm( int cardinality, int i ){
  return d_totality_terms[0][i];
  //}else{
  //  return d_totality_terms[cardinality][i];
  //}
}

void StrongSolverTheoryUF::SortModel::simpleCheckCardinality() {
  if( d_maxNegCard.get()!=0 && d_hasCard.get() && d_cardinality.get()<d_maxNegCard.get() ){
    Node lem = NodeManager::currentNM()->mkNode( AND, getCardinalityLiteral( d_cardinality.get() ),
                                                      getCardinalityLiteral( d_maxNegCard.get() ).negate() );
    Trace("uf-ss-lemma") << "*** Simple cardinality conflict : " << lem << std::endl;
    d_thss->getOutputChannel().conflict( lem );
    d_thss->d_conflict.set( true );
  }
}

void StrongSolverTheoryUF::SortModel::debugPrint( const char* c ){
  Debug( c ) << "--  Conflict Find:" << std::endl;
  Debug( c ) << "Number of reps = " << d_reps << std::endl;
  Debug( c ) << "Cardinality req = " << d_cardinality << std::endl;
  unsigned debugReps = 0;
  for( int i=0; i<(int)d_regions_index; i++ ){
    if( d_regions[i]->d_valid ){
      Debug( c ) << "Region #" << i << ": " << std::endl;
      d_regions[i]->debugPrint( c, true );
      Debug( c ) << std::endl;
      for( std::map< Node, Region::RegionNodeInfo* >::iterator it = d_regions[i]->d_nodes.begin(); it != d_regions[i]->d_nodes.end(); ++it ){
        if( it->second->d_valid ){
          if( d_regions_map[ it->first ]!=i ){
            Debug( c ) << "***Bad regions map : " << it->first << " " << d_regions_map[ it->first ].get() << std::endl;
          }
        }
      }
      debugReps += d_regions[i]->getNumReps();
    }
  }
  if( debugReps!=d_reps ){
    Debug( c ) << "***Bad reps: " << d_reps << ", actual = " << debugReps << std::endl;
  }
}

bool StrongSolverTheoryUF::SortModel::debugModel( TheoryModel* m ){
  if( Trace.isOn("uf-ss-warn") ){
    std::vector< Node > eqcs;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( m->d_equalityEngine );
    while( !eqcs_i.isFinished() ){
      Node eqc = (*eqcs_i);
      if( eqc.getType()==d_type ){
        if( std::find( eqcs.begin(), eqcs.end(), eqc )==eqcs.end() ){
          eqcs.push_back( eqc );
          //we must ensure that this equivalence class has been accounted for
          if( d_regions_map.find( eqc )==d_regions_map.end() ){
            Trace("uf-ss-warn") << "WARNING : equivalence class " << eqc << " unaccounted for." << std::endl;
            Trace("uf-ss-warn") << "  type : " << d_type << std::endl;
            Trace("uf-ss-warn") << "  kind : " << eqc.getKind() << std::endl;
          }
        }
      }
      ++eqcs_i;
    }
  }
  int nReps = m->d_rep_set.d_type_reps.find( d_type )==m->d_rep_set.d_type_reps.end() ? 0 : (int)m->d_rep_set.d_type_reps[d_type].size();
  if( nReps!=(d_maxNegCard+1) ){
    Trace("uf-ss-warn") << "WARNING : Model does not have same # representatives as cardinality for " << d_type << "." << std::endl;
    Trace("uf-ss-warn") << "   Max neg cardinality : " << d_maxNegCard << std::endl;
    Trace("uf-ss-warn") << "   # Reps : " << nReps << std::endl;
    if( d_maxNegCard>=nReps ){
      /*
      for( unsigned i=0; i<d_fresh_aloc_reps.size(); i++ ){
        if( add>0 && !m->d_equalityEngine->hasTerm( d_fresh_aloc_reps[i] ) ){
          m->d_rep_set.d_type_reps[d_type].push_back( d_fresh_aloc_reps[i] );
          add--;
        }
      }
      for( int i=0; i<add; i++ ){
        std::stringstream ss;
        ss << "r_" << d_type << "_";
        Node nn = NodeManager::currentNM()->mkSkolem( ss.str(), d_type, "enumeration to meet negative card constraint" );
        d_fresh_aloc_reps.push_back( nn );
        m->d_rep_set.d_type_reps[d_type].push_back( nn );
      }
      */
      while( (int)d_fresh_aloc_reps.size()<=d_maxNegCard ){
        std::stringstream ss;
        ss << "r_" << d_type << "_";
        Node nn = NodeManager::currentNM()->mkSkolem( ss.str(), d_type, "enumeration to meet negative card constraint" );
        d_fresh_aloc_reps.push_back( nn );
      }
      if( d_maxNegCard==1 ){
        m->d_rep_set.d_type_reps[d_type].push_back( d_fresh_aloc_reps[0] );
      }else{
        //must add lemma
        std::vector< Node > force_cl;
        for( int i=0; i<=d_maxNegCard; i++ ){
          for( int j=(i+1); j<=d_maxNegCard; j++ ){
            force_cl.push_back( d_fresh_aloc_reps[i].eqNode( d_fresh_aloc_reps[j] ).negate() );
          }
        }
        Node cl = getCardinalityLiteral( d_maxNegCard );
        Node lem = NodeManager::currentNM()->mkNode( OR, cl, NodeManager::currentNM()->mkNode( AND, force_cl ) );
        Trace("uf-ss-lemma") << "*** Enforce negative cardinality constraint lemma : " << lem << std::endl;
        d_thss->getOutputChannel().lemma( lem );
        return false;
      }
    }
  }
  return true;
}

int StrongSolverTheoryUF::SortModel::getNumRegions(){
  int count = 0;
  for( int i=0; i<(int)d_regions_index; i++ ){
    if( d_regions[i]->d_valid ){
      count++;
    }
  }
  return count;
}

Node StrongSolverTheoryUF::SortModel::getCardinalityLiteral( int c ) {
  if( d_cardinality_literal.find( c )==d_cardinality_literal.end() ){
    d_cardinality_literal[c] = NodeManager::currentNM()->mkNode( CARDINALITY_CONSTRAINT, d_cardinality_term,
                                                                 NodeManager::currentNM()->mkConst( Rational( c ) ) );
  }
  return d_cardinality_literal[c];
}

StrongSolverTheoryUF::StrongSolverTheoryUF(context::Context* c, context::UserContext* u, OutputChannel& out, TheoryUF* th) :
d_out( &out ), d_th( th ), d_conflict( c, false ), d_rep_model(), d_aloc_com_card( u, 0 ), d_com_card_assertions( c ),
d_card_assertions_eqv_lemma( u ), d_rel_eqc( c )
{
  if( options::ufssDiseqPropagation() ){
    d_deq_prop = new DisequalityPropagator( th->getQuantifiersEngine(), this );
  }else{
    d_deq_prop = NULL;
  }
  if( options::ufssSymBreak() ){
    d_sym_break = new SubsortSymmetryBreaker( th->getQuantifiersEngine(), c );
  }else{
    d_sym_break = NULL;
  }
}

SortInference* StrongSolverTheoryUF::getSortInference() {
  return d_th->getQuantifiersEngine()->getTheoryEngine()->getSortInference();
}

/** get default sat context */
context::Context* StrongSolverTheoryUF::getSatContext() {
  return d_th->getSatContext();
}

/** get default output channel */
OutputChannel& StrongSolverTheoryUF::getOutputChannel() {
  return d_th->getOutputChannel();
}

/** ensure eqc */
void StrongSolverTheoryUF::ensureEqc( SortModel* c, Node a ) {
  if( !hasEqc( a ) ){
    d_rel_eqc[a] = true;
    Trace("uf-ss-solver") << "StrongSolverTheoryUF: New eq class " << a << " : " << a.getType() << std::endl;
    c->newEqClass( a );
    if( options::ufssSymBreak() ){
      d_sym_break->newEqClass( a );
    }
    Trace("uf-ss-solver") << "StrongSolverTheoryUF: Done New eq class." << std::endl;
  }
}

void StrongSolverTheoryUF::ensureEqcRec( Node n ) {
  if( !hasEqc( n ) ){
    SortModel* c = getSortModel( n );
    if( c ){
      ensureEqc( c, n );
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      ensureEqcRec( n[i] );
    }
  }
}

/** has eqc */
bool StrongSolverTheoryUF::hasEqc( Node a ) {
  NodeBoolMap::iterator it = d_rel_eqc.find( a );
  return it!=d_rel_eqc.end() && (*it).second;
}

/** new node */
void StrongSolverTheoryUF::newEqClass( Node n ){
  SortModel* c = getSortModel( n );
  if( c ){
    //do nothing
  }
}

/** merge */
void StrongSolverTheoryUF::merge( Node a, Node b ){
  //TODO: ensure they are relevant
  SortModel* c = getSortModel( a );
  if( c ){
    ensureEqc( c, a );
    if( hasEqc( b ) ){
      Trace("uf-ss-solver") << "StrongSolverTheoryUF: Merge " << a << " " << b << " : " << a.getType() << std::endl;
      c->merge( a, b );
      Trace("uf-ss-solver") << "StrongSolverTheoryUF: Done Merge." << std::endl;
    }else{
      //c->assignEqClass( b, a );
      d_rel_eqc[b] = true;
    }
  }else{
    if( options::ufssDiseqPropagation() ){
      d_deq_prop->merge(a, b);
    }
  }
}

/** assert terms are disequal */
void StrongSolverTheoryUF::assertDisequal( Node a, Node b, Node reason ){
  SortModel* c = getSortModel( a );
  if( c ){
    ensureEqc( c, a );
    ensureEqc( c, b );
    Trace("uf-ss-solver") << "StrongSolverTheoryUF: Assert disequal " << a << " " << b << " : " << a.getType() << std::endl;
    //Assert( d_th->d_equalityEngine.getRepresentative( a )==a );
    //Assert( d_th->d_equalityEngine.getRepresentative( b )==b );
    c->assertDisequal( a, b, reason );
    Trace("uf-ss-solver") << "StrongSolverTheoryUF: Done Assert disequal." << std::endl;
  }else{
    if( options::ufssDiseqPropagation() ){
      d_deq_prop->assertDisequal(a, b, reason);
    }
  }
}

/** assert a node */
void StrongSolverTheoryUF::assertNode( Node n, bool isDecision ){
  Trace("uf-ss") << "Assert " << n << " " << isDecision << std::endl;
  ensureEqcRec( n );
  bool polarity = n.getKind() != kind::NOT;
  TNode lit = polarity ? n : n[0];
  if( lit.getKind()==CARDINALITY_CONSTRAINT ){
    TypeNode tn = lit[0].getType();
    Assert( tn.isSort() );
    Assert( d_rep_model[tn] );
    long nCard = lit[1].getConst<Rational>().getNumerator().getLong();
    Node ct = d_rep_model[tn]->getCardinalityTerm();
    if( lit[0]==ct ){
      d_rep_model[tn]->assertCardinality( d_out, nCard, polarity );
      //check if combined cardinality is violated
      checkCombinedCardinality();
    }else{
      //otherwise, make equal via lemma
      if( d_card_assertions_eqv_lemma.find( lit )==d_card_assertions_eqv_lemma.end() ){
        Node eqv_lit = NodeManager::currentNM()->mkNode( CARDINALITY_CONSTRAINT, ct, lit[1] );
        Trace("uf-ss-lemma") << "*** Cardinality equiv lemma : " << lit.iffNode( eqv_lit ) << std::endl;
        getOutputChannel().lemma( lit.iffNode( eqv_lit ) );
        d_card_assertions_eqv_lemma[lit] = true;
      }
    }
  }else if( lit.getKind()==COMBINED_CARDINALITY_CONSTRAINT ){
    d_com_card_assertions[lit] = polarity;
    if( polarity ){
      checkCombinedCardinality();
    }else{
      bool needsCard = true;
      for( std::map< int, Node >::iterator it = d_com_card_literal.begin(); it != d_com_card_literal.end(); ++it ){
        if( d_com_card_assertions.find( it->second )==d_com_card_assertions.end() || d_com_card_assertions[it->second] ){
          needsCard = false;
          break;
        }
      }
      if( needsCard ){
        allocateCombinedCardinality();
      }
    }
  }else{
    if( Trace.isOn("uf-ss-warn") ){
      ////FIXME: this is too strict: theory propagations are showing up as isDecision=true, but
      ////       a theory propagation is not a decision.
      if( isDecision ){
        for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
          if( !it->second->hasCardinalityAsserted() ){
            Trace("uf-ss-warn") << "WARNING: Assert " << n << " as a decision before cardinality for " << it->first << "." << std::endl;
            //Message() << "Error: constraint asserted before cardinality for " << it->first << std::endl;
            //Unimplemented();
          }
        }
      }
    }
    if( lit.getKind()!=EQUAL ){
      //it is a predicate
      if( options::ufssDiseqPropagation() ){
        d_deq_prop->assertPredicate(lit, polarity);
      }
    }
  }
  Trace("uf-ss") << "Assert: done " << n << " " << isDecision << std::endl;
}

bool StrongSolverTheoryUF::areDisequal( Node a, Node b ) {
  if( a==b ){
    return false;
  }else{
    a = d_th->d_equalityEngine.getRepresentative( a );
    b = d_th->d_equalityEngine.getRepresentative( b );
    if( d_th->d_equalityEngine.areDisequal( a, b, false ) ){
      return true;
    }else{
      SortModel* c = getSortModel( a );
      if( c ){
        return c->areDisequal( a, b );
      }else{
        return false;
      }
    }
  }
}

/** check */
void StrongSolverTheoryUF::check( Theory::Effort level ){
  if( !d_conflict ){
    Trace("uf-ss-solver") << "StrongSolverTheoryUF: check " << level << std::endl;
    if( level==Theory::EFFORT_FULL && Debug.isOn( "uf-ss-debug" ) ){
      debugPrint( "uf-ss-debug" );
    }
    for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
      it->second->check( level, d_out );
      if( it->second->isConflict() ){
        d_conflict = true;
        break;
      }
    }
    //check symmetry breaker
    if( !d_conflict && options::ufssSymBreak() ){
      d_sym_break->check( level );
    }
    Trace("uf-ss-solver") << "Done StrongSolverTheoryUF: check " << level << std::endl;
  }
}

/** propagate */
void StrongSolverTheoryUF::propagate( Theory::Effort level ){
  //for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
  //  it->second->propagate( level, d_out );
  //}
}

/** get next decision request */
Node StrongSolverTheoryUF::getNextDecisionRequest(){
  //request the combined cardinality as a decision literal, if not already asserted
  if( options::ufssFairness() ){
    int comCard = 0;
    Node com_lit;
    do {
      com_lit = d_com_card_literal.find( comCard )!=d_com_card_literal.end() ? d_com_card_literal[comCard] : Node::null();
      if( !com_lit.isNull() && d_com_card_assertions.find( com_lit )==d_com_card_assertions.end() ){
        Trace("uf-ss-dec") << "Decide on combined cardinality : " << com_lit << std::endl;
        return com_lit;
      }
      comCard++;
    }while( !com_lit.isNull() );
  }
  //otherwise, check each individual sort
  for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
    Node n = it->second->getNextDecisionRequest();
    if( !n.isNull() ){
      return n;
    }
  }
  return Node::null();
}

void StrongSolverTheoryUF::preRegisterTerm( TNode n ){
  //initialize combined cardinality
  initializeCombinedCardinality();

  Trace("uf-ss-register") << "Preregister " << n << "." << std::endl;
  //shouldn't have to preregister this type (it may be that there are no quantifiers over tn)
  TypeNode tn = n.getType();
  if( d_rep_model.find( tn )==d_rep_model.end() ){
    SortModel* rm = NULL;
    if( tn.isSort() ){
      Trace("uf-ss-register") << "Preregister sort " << tn << "." << std::endl;
      rm  = new SortModel( n, d_th->getSatContext(), d_th->getUserContext(), this );
      //getOutputChannel().lemma( n.eqNode( rm->getCardinalityTerm() ) );
    }else{
      /*
      if( tn==NodeManager::currentNM()->integerType() || tn==NodeManager::currentNM()->realType() ){
        Debug("uf-ss-na") << "Error: Cannot perform finite model finding on arithmetic quantifier";
        Debug("uf-ss-na") << " (" << f << ")";
        Debug("uf-ss-na") << std::endl;
        Unimplemented("Cannot perform finite model finding on arithmetic quantifier");
      }else if( tn.isDatatype() ){
        Debug("uf-ss-na") << "Error: Cannot perform finite model finding on datatype quantifier";
        Debug("uf-ss-na") << " (" << f << ")";
        Debug("uf-ss-na") << std::endl;
        Unimplemented("Cannot perform finite model finding on datatype quantifier");
      }
      */
    }
    if( rm ){
      rm->initialize( d_out );
      d_rep_model[tn] = rm;
      //d_rep_model_init[tn] = true;
    }
  }else{
    Trace("uf-ss-register") << "Already preregistered sort " << tn << "." << std::endl;
  }
}

void StrongSolverTheoryUF::registerQuantifier( Node f ){
  Debug("uf-ss-register") << "Register quantifier " << f << std::endl;
  //must ensure the quantifier does not quantify over arithmetic
  //for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
  //  TypeNode tn = f[0][i].getType();
  //  preRegisterType( tn, true );
  //}
}


StrongSolverTheoryUF::SortModel* StrongSolverTheoryUF::getSortModel( Node n ){
  TypeNode tn = n.getType();
  std::map< TypeNode, SortModel* >::iterator it = d_rep_model.find( tn );
  //pre-register the type if not done already
  if( it==d_rep_model.end() ){
    preRegisterTerm( n );
    it = d_rep_model.find( tn );
  }
  if( it!=d_rep_model.end() ){
    //initialize the type if necessary
    //if( d_rep_model_init.find( tn )==d_rep_model_init.end() ){
      ////initialize the model
      //it->second->initialize( d_out );
      //d_rep_model_init[tn] = true;
    //}
    return it->second;
  }
  return NULL;
}

void StrongSolverTheoryUF::notifyRestart(){

}

/** get cardinality for sort */
int StrongSolverTheoryUF::getCardinality( Node n ) {
  SortModel* c = getSortModel( n );
  if( c ){
    return c->getCardinality();
  }else{
    return -1;
  }
}

int StrongSolverTheoryUF::getCardinality( TypeNode tn ) {
  std::map< TypeNode, SortModel* >::iterator it = d_rep_model.find( tn );
  if( it!=d_rep_model.end() && it->second ){
    return it->second->getCardinality();
  }
  return -1;
}

bool StrongSolverTheoryUF::minimize( TheoryModel* m ){
  for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
    if( !it->second->minimize( d_out, m ) ){
      return false;
    }
  }
  for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
    Trace("uf-ss-minimize") << "Cardinality( " << it->first << " ) : " << it->second->getCardinality() << std::endl;
  }
  return true;
}

//print debug
void StrongSolverTheoryUF::debugPrint( const char* c ){
  //EqClassesIterator< TheoryUF::NotifyClass > eqc_iter( &((TheoryUF*)d_th)->d_equalityEngine );
  //while( !eqc_iter.isFinished() ){
  //  Debug( c ) << "Eq class [[" << (*eqc_iter) << "]]" << std::endl;
  //  EqClassIterator< TheoryUF::NotifyClass > eqc_iter2( *eqc_iter, &((TheoryUF*)d_th)->d_equalityEngine );
  //  Debug( c ) << "   ";
  //  while( !eqc_iter2.isFinished() ){
  //    Debug( c ) << "[" << (*eqc_iter2) << "] ";
  //    eqc_iter2++;
  //  }
  //  Debug( c ) << std::endl;
  //  eqc_iter++;
  //}

  for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
    Debug( c ) << "Conflict find structure for " << it->first << ": " << std::endl;
    it->second->debugPrint( c );
    Debug( c ) << std::endl;
  }
}

bool StrongSolverTheoryUF::debugModel( TheoryModel* m ){
  for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
    if( !it->second->debugModel( m ) ){
      return false;
    }
  }
  return true;
}

/** initialize */
void StrongSolverTheoryUF::initializeCombinedCardinality() {
  if( options::ufssFairness() ){
    Trace("uf-ss-com-card-debug") << "Initialize combined cardinality" << std::endl;
    if( d_aloc_com_card.get()==0 ){
      allocateCombinedCardinality();
    }
  }
}

/** check */
void StrongSolverTheoryUF::checkCombinedCardinality() {
  if( options::ufssFairness() ){
    int totalCombinedCard = 0;
    for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
      totalCombinedCard += it->second->getMaximumNegativeCardinality();
    }
    Trace("uf-ss-com-card-debug") << "Check combined cardinality, total combined card : " << totalCombinedCard << std::endl;
    for( int i=0; i<totalCombinedCard; i++ ){
      if( d_com_card_literal.find( i )!=d_com_card_literal.end() ){
        Node com_lit = d_com_card_literal[i];
        if( d_com_card_assertions.find( com_lit )!=d_com_card_assertions.end() && d_com_card_assertions[com_lit] ){
          //conflict
          std::vector< Node > conf;
          conf.push_back( com_lit );
          int totalAdded = 0;
          for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
            int c = it->second->getMaximumNegativeCardinality();
            if( c>0 ){
              conf.push_back( it->second->getCardinalityLiteral( c ).negate() );
              totalAdded += c;
            }
            if( totalAdded>i ){
              break;
            }
          }
          Node cc = NodeManager::currentNM()->mkNode( AND, conf );
          Trace("uf-ss-lemma") << "*** Combined cardinality conflict : " << cc << std::endl;
          Trace("uf-ss-com-card") << "*** Combined cardinality conflict : " << cc << std::endl;
          getOutputChannel().conflict( cc );
          d_conflict.set( true );
        }
      }
    }
  }
}

void StrongSolverTheoryUF::allocateCombinedCardinality() {
  Trace("uf-ss-com-card") << "Allocate combined cardinality (" << d_aloc_com_card.get() << ")" << std::endl;
  //make node
  Node lem = NodeManager::currentNM()->mkNode( COMBINED_CARDINALITY_CONSTRAINT,
                                               NodeManager::currentNM()->mkConst( Rational( d_aloc_com_card.get() ) ) );
  Trace("uf-ss-com-card") << "Split on " << lem << std::endl;
  lem = Rewriter::rewrite(lem);
  d_com_card_literal[ d_aloc_com_card.get() ] = lem;
  lem = NodeManager::currentNM()->mkNode( OR, lem, lem.notNode() );
  //add as lemma to output channel
  getOutputChannel().lemma( lem );
  //require phase
  getOutputChannel().requirePhase( d_com_card_literal[ d_aloc_com_card.get() ], true );
  //increment cardinality
  d_aloc_com_card.set( d_aloc_com_card.get() + 1 );
}

StrongSolverTheoryUF::Statistics::Statistics():
  d_clique_conflicts("StrongSolverTheoryUF::Clique_Conflicts", 0),
  d_clique_lemmas("StrongSolverTheoryUF::Clique_Lemmas", 0),
  d_split_lemmas("StrongSolverTheoryUF::Split_Lemmas", 0),
  d_disamb_term_lemmas("StrongSolverTheoryUF::Disambiguate_Term_Lemmas", 0),
  d_sym_break_lemmas("StrongSolverTheoryUF::Symmetry_Breaking_Lemmas", 0),
  d_totality_lemmas("StrongSolverTheoryUF::Totality_Lemmas", 0),
  d_max_model_size("StrongSolverTheoryUF::Max_Model_Size", 1)
{
  StatisticsRegistry::registerStat(&d_clique_conflicts);
  StatisticsRegistry::registerStat(&d_clique_lemmas);
  StatisticsRegistry::registerStat(&d_split_lemmas);
  StatisticsRegistry::registerStat(&d_disamb_term_lemmas);
  StatisticsRegistry::registerStat(&d_sym_break_lemmas);
  StatisticsRegistry::registerStat(&d_totality_lemmas);
  StatisticsRegistry::registerStat(&d_max_model_size);
}

StrongSolverTheoryUF::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_clique_conflicts);
  StatisticsRegistry::unregisterStat(&d_clique_lemmas);
  StatisticsRegistry::unregisterStat(&d_split_lemmas);
  StatisticsRegistry::unregisterStat(&d_disamb_term_lemmas);
  StatisticsRegistry::unregisterStat(&d_sym_break_lemmas);
  StatisticsRegistry::unregisterStat(&d_totality_lemmas);
  StatisticsRegistry::unregisterStat(&d_max_model_size);
}


DisequalityPropagator::DisequalityPropagator(QuantifiersEngine* qe, StrongSolverTheoryUF* ufss) :
  d_qe(qe), d_ufss(ufss){
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
}

void DisequalityPropagator::checkEquivalenceClass( Node t, Node eqc ) {
  if( t.getKind()==APPLY_UF ){
    Node op = t.getOperator();
    eqc = d_ufss->getTheory()->getEqualityEngine()->getRepresentative( eqc );
    eq::EqClassIterator eqc_i(eqc, d_ufss->getTheory()->getEqualityEngine());
    while( !eqc_i.isFinished() ){
      Node s = *eqc_i;
      if( s.getKind()==APPLY_UF && s.getOperator()==op ){
        int unkIndex = -1;
        for( size_t i=0; i<t.getNumChildren(); i++ ){
          //should consult strong solver since it knows more disequalities
          if( d_ufss->areDisequal( t[i], s[i] ) ){
          //if( d_qe->getEqualityQuery()->areDisequal( t[i], s[i] ) ){
            unkIndex = -1;
            break;
          }else if( !d_qe->getEqualityQuery()->areEqual( t[i], s[i] ) ){
            if( unkIndex==-1 ){
              unkIndex = i;
            }else{
              unkIndex = -1;
              break;
            }
          }
        }
        if( unkIndex!=-1 ){
          Trace("deq-prop") << "propagate disequality " << t[unkIndex] << " " << s[unkIndex] << std::endl;
          d_ufss->assertDisequal(t[unkIndex], s[unkIndex], Node::null());
          ++( d_statistics.d_propagations );
          if( d_ufss->isConflict() ){
            return;
          }
        }
      }
      ++eqc_i;
    }
  }
}

/** merge */
void DisequalityPropagator::merge( Node a, Node b ){

}

/** assert terms are disequal */
void DisequalityPropagator::assertDisequal( Node a, Node b, Node reason ){
  Trace("deq-prop") << "Notify disequal : " << a << " " << b << std::endl;
}


void DisequalityPropagator::assertPredicate( Node p, bool polarity ) {
  Trace("deq-prop") << "Assert predicate : " << p << " " << polarity << std::endl;
  checkEquivalenceClass( p, polarity ? d_false : d_true );
}

DisequalityPropagator::Statistics::Statistics():
   d_propagations("StrongSolverTheoryUF::Disequality_Propagations", 0)
{
  StatisticsRegistry::registerStat(& d_propagations);
}

DisequalityPropagator::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(& d_propagations);
}
