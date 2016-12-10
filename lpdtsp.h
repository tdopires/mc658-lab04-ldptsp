/*******************************************************************************
 * VERSION: 1.6
 * MC658 - Projeto e Análise de Algoritmos III - 2s2016
 * Prof.: Flavio Keidi Miyazawa
 * PED: Mauro Henrique Mulati
 ******************************************************************************/

/* Atenção: Qualquer alteração neste arquivo não terá efeito no projeto a ser 
 * testado no Momento da avaliação. */

#ifndef LPDTSP_H
#define LPDTSP_H

#include "mygraphlib.h"
typedef ListDigraph::NodeMap<ListDigraph::Node> DNodeNodeMap;

typedef enum ENUM_ALG
{
   NONE,
   CONSTR_HEUR,
   META_HEUR,
   EXACT,
} ALG;

typedef enum ENUM_VERBOSITY
{
   QUIET,
   VERB,
   GRAPH
} VERBOSITY;

typedef struct structParams
{
   ALG       alg;
   int       timeLimit;
   VERBOSITY verbosity;
   string    inputFile;
   string    outputFile;
} Params;

typedef struct structItem
{
   int i;
   DNode s;
   DNode t;
   double w;
} Item;

class LpdTspInstance
{
public:
   LpdTspInstance(Digraph        &pg,
                  DNodeStringMap &pvname,
                  ArcValueMap    &pweight,
                  DNodePosMap    &pposx,
                  DNodePosMap    &pposy,
                  DNode           pdepot,
                  double          pcapacity,
                  vector<Item>   &pitems,
                  DNodeIntMap    &ps,
                  DNodeIntMap    &pt);
   
   ListDigraph    &g;
   int             n,
                   m;
   DNodeStringMap &vname;
   ArcStringMap    aname;
   DNodeColorMap   vcolor;
   ArcColorMap     acolor;
   ArcValueMap    &weight;
   DNodePosMap    &posx;
   DNodePosMap    &posy;

   DNode           depot;
   double          capacity;
   int             k;
   vector<Item>   &items;
   
   DNodeIntMap    &s;  // Pickup the item s in the DNode. If 0, it is not a pickup DNode.
   DNodeIntMap    &t;  // Delivery the item t in the DNode. If 0, it is not a delivery DNode.
};

class LpdTspSolution
{
public:
   LpdTspSolution();
   vector<DNode> tour;
   double        lowerBound;
   double        cost;
   double        upperBound;
};

typedef enum ENUM_SOLUTION_STATUS
{
   NOT_FOUND_FEASIBLE_SOLUTION,
   INCOMPATIBLES_COST_AND_OPTIMAL,
   INVALID_DNODE,
   FIRST_IS_NOT_DEPOT,
   ARC_MISSING,
   PICKUP_DELIVERY_ORDER_ERROR,
   ITEM_NOT_PICKED_UP,
   NEGATIVE_LOAD_ERROR,
   CAPACITY_EXCEDED,
   REMAINING_LOAD_ERROR,
   ITEM_NOT_DELIVERED,
   COST_ERROR,
   COST_BOUND_ERROR,
   INVALID_BOUNDS_OPT,
   OK
} SOLUTION_STATUS;

void            readCheckParams(Params &params, int argc, char *argv[]);
void            showUsage();
void            PulaBrancoComentario(ifstream &ifile);  // Implemented in mygraphlib.cpp
bool            readListDigraphLpdTsp(string          filename,
                                      ListDigraph    &g,
                                      DNodeStringMap &vname,
                                      ArcValueMap    &weight,
                                      DNodePosMap    &posx,
                                      DNodePosMap    &posy,
                                      const bool      dupla,
                                      DNode          &depot,
                                      double         &capacity,
                                      vector<Item>   &items);  // Different version of the one in mygraphlib
SOLUTION_STATUS checkSolutionStatus(LpdTspInstance &instance,
                                    LpdTspSolution &sol,
                                    bool optimal);
string          decodeSolutionStatus(SOLUTION_STATUS solutionStatus);
void            solutionAsGraphical(LpdTspInstance &l, LpdTspSolution  &s, string inputFile);
string          instanceAsString(LpdTspInstance &lpdTspInstance);
string          instanceDescriptionAsString(LpdTspInstance &instance);
string          dnodesAndItemsAsString(LpdTspInstance &l);
string          arcsAndItemsAsString(LpdTspInstance &l);
inline string   vti(DNode v, LpdTspInstance &l);
string          itemsAsString(LpdTspInstance &l);
string          solutionAsString(LpdTspInstance &lpdTspInstance, LpdTspSolution  &lpdTspSolution);
string          tourAsString(LpdTspInstance &lpdTspInstance, LpdTspSolution  &lpdTspSolution);
string          tourAndItemsAsString(LpdTspInstance &lpdTspInstance, LpdTspSolution  &lpdTspSolution);
string          valuesAsString(LpdTspSolution &lpdTspSolution);
string          resultAsString(LpdTspInstance  &lpdTspInstance,
                              LpdTspSolution  &lpdTspSolution,
                              Params          &params,
                              bool             optimal,
                              SOLUTION_STATUS  solutionStatus,
                              int              elapsedTime);
string          decodeAlg(ALG alg);

#endif
