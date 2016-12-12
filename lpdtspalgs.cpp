/*******************************************************************************
 * MC658 - Projeto e Análise de Algoritmos III - 2s2016
 * Prof.: Flavio Keidi Miyazawa
 * PED: Mauro Henrique Mulati
 ******************************************************************************/

/* IMPLEMENTE AS FUNCOES INDICADAS
 * DIGITE SEU RA: 123153
 * SUBMETA SOMENTE ESTE ARQUIVO */

#include "gurobi_c++.h"
#include <set>
#include <lemon/unionfind.h>
#include <lemon/gomory_hu.h>
#include <lemon/tolerance.h>
#include <lemon/hao_orlin.h>
#include <lemon/adaptors.h>
#include <iostream>
#include <float.h>
#include <lemon/list_graph.h>
#include "mygraphlib.h"
#include "lpdtspalgs.h"

#define GUROBI_NEWVERSION 1

//#define MY_EPS 0.01

//------------------------------------------------------------------------------
bool naive(const LpdTspInstance &instance, LpdTspSolution  &sol, int tl)
/*
 * Algoritmo ingênuo para o LPD-TSP. Ideia:
 * constrNaiveHeur(l, s)
 *    s.tour.push_back(l.depot)
 *    while(s.tour.size() < 2*l.k+1)
 *       v = argmin_{v' in V} {d_{(v,v')} | (v' é adj a v) e ((v' é s) ou (v' é t de i cujo s é u em l.tour))}
 *       l.tour.push_back(v)
 */
{
    DNode v,
         vl;

    double vval,
          vlval;

    int i;

    sol.tour.clear();
    sol.cost = 0.0;

    v = instance.depot;
    sol.tour.push_back(v);

    while((int)sol.tour.size() < 2 * instance.k + 1 && v != INVALID){
        v    = INVALID;
        vval = DBL_MAX;

        for(OutArcIt o(instance.g, sol.tour.back()); o != INVALID; ++o){
            vl    = instance.g.target(o);
            vlval = DBL_MAX;

            i = 0;
            while(i < (int)sol.tour.size() && vl != sol.tour[i]) i++;
            if(i < (int)sol.tour.size()) continue;

            if(instance.s[vl] > 0){  // If DNode vl is start of an item
                vlval = instance.weight[o];
            }
            else if(instance.t[vl] > 0){  // If DNode vl is término of an item
                i = 0;
                while(i < (int)sol.tour.size() && instance.t[ vl ] != instance.s[ sol.tour[i] ]){  // Look for the start DNode of the item which terminates in DNode vl
                i++;
                }
                if(i < (int)sol.tour.size()){
                    vlval = instance.weight[o];
                }
            }

            if(vlval < vval){
                v    = vl;
                vval = vlval;
            }
        }

        if(v != INVALID){
            sol.tour.push_back(v);
            sol.cost += vval;
        }
    }

    if(v == INVALID){
        sol.cost = DBL_MAX;
    }
    else{
        OutArcIt o(instance.g, sol.tour.back());
        for(; o != INVALID; ++o){
            if(instance.g.target(o) == sol.tour.front()) break;
        }
        if(o != INVALID){
            sol.cost += instance.weight[o];
        }
    }

    return false;
}
//------------------------------------------------------------------------------


bool contains_node(vector<DNode> &list, DNode node)
{
    for(auto i = list.begin(); i != list.end(); ++i){
        if(*i == node){
            return true;
        }
    }
   return false;
}

bool v1_f_insertion(const LpdTspInstance &l, LpdTspSolution &s, DNodeIntMap &h, vector<int> &items_status, double &capacityCheck, clock_t beginExec, int tl)
{
    if (((clock() - beginExec) / CLOCKS_PER_SEC) > (tl-0.01))
        return false;

    if (s.tour.size() == 2 * l.k + 1)
        return true;

    DNode node_to_insert = INVALID;
    double node_to_insert_cost = 0.0;
   
    bool find_node_to_insert = true;
    vector<DNode> black_list = vector<DNode>();

    while (find_node_to_insert) {
        DNode min_delivery_node = INVALID;
        DNode min_pickup_node = INVALID;
        double min_delivery_cost = DBL_MAX;
        double min_pickup_cost = DBL_MAX;

        for(OutArcIt o(l.g, s.tour.back()); o != INVALID; ++o){
            DNode targetNode = l.g.target(o);

            if (h[targetNode] || contains_node(black_list, targetNode))
                continue;

            int s = l.s[ targetNode ];
            // is a Pickup node and item was not picked up and item weight will not be over capacity
            if(s != 0 && items_status[s-1] == 0 && capacityCheck + l.items[s-1].w <= l.capacity && l.weight[o] < min_pickup_cost) {
                min_pickup_cost = l.weight[o];
                min_pickup_node = targetNode;
            }

            int t = l.t[ targetNode ];
            // is a Delivery node and item was already picked up
            if(t != 0 && items_status[t-1] == 1 && l.weight[o] < min_delivery_cost) {
                min_delivery_cost = l.weight[o];
                min_delivery_node = targetNode;
            }
        }

        if (min_delivery_node != INVALID || min_pickup_node != INVALID) {
            double r = ((double) rand() / (RAND_MAX)); // r is a random probability
            if (min_pickup_node == INVALID)
                r = 0.0; // if we just have a delivery node and don't have a pickup node
            else if (min_delivery_node == INVALID)
                r = 1.0; // if we just have a pickup node and don't have a delivery node

            if (r < 0.5) {
                int itemNo = l.t[ min_delivery_node ] - 1;
                capacityCheck -= l.items[itemNo].w;
                items_status[itemNo] = 2;

                node_to_insert = min_delivery_node;
                node_to_insert_cost = min_delivery_cost;
            } else {
                int itemNo = l.s[ min_pickup_node ] - 1;
                capacityCheck += l.items[itemNo].w;
                items_status[itemNo] = 1;

                node_to_insert = min_pickup_node;
                node_to_insert_cost = min_pickup_cost;
            }

            s.tour.push_back(node_to_insert);
            h[node_to_insert] = 1;
            s.cost += node_to_insert_cost;

            bool insertion_ok = v1_f_insertion(l, s, h, items_status, capacityCheck, beginExec, tl);
            if (!insertion_ok) {
                s.tour.erase(s.tour.end() - 1);
                h[node_to_insert] = 0;
                s.cost -= node_to_insert_cost;

                if (r <= 0.5) {
                    int itemNo = l.t[ min_delivery_node ] - 1;
                    capacityCheck += l.items[itemNo].w;
                    items_status[itemNo] = 1;
                } else {
                    int itemNo = l.s[ min_pickup_node ] - 1;
                    capacityCheck -= l.items[itemNo].w;
                    items_status[itemNo] = 0;
                }
                
                black_list.push_back(node_to_insert);
            } else {
                return true;
            }
        } else {
            find_node_to_insert = false;
        }
    }
   
    // we didn't find a valid node to insert
    return false;
}

//------------------------------------------------------------------------------
bool constrHeur_v1_f_insertion(const LpdTspInstance &l, LpdTspSolution  &s, int tl)
{
    clock_t beginExec = clock();

    s.tour.clear();
    s.cost = 0.0;

    DNodeIntMap h(l.g);
    for(DNodeIt v(l.g); v != INVALID; ++v){
        h[v] = 0;
    }

    s.tour.push_back(l.depot);
    h[l.depot] = 1;

    vector<int> items_status(l.k, 0); // 0 para item não pego, 1 para item pego, 2 para entregue
    double capacityCheck = 0.0;

    v1_f_insertion(l, s, h, items_status, capacityCheck, beginExec, tl);

    for (OutArcIt o(l.g, s.tour.back()); o != INVALID; ++o){
        if (l.g.target(o) == l.depot) {
            s.cost += l.weight[o];
        }
    }

    return false;
}

//------------------------------------------------------------------------------
bool constrHeur(const LpdTspInstance &l, LpdTspSolution  &s, int tl)
/* Implemente esta função, entretanto, não altere sua assinatura */
{
    return constrHeur_v1_f_insertion(l, s, tl);
}

//------------------------------------------------------------------------------
bool metaHeur(const LpdTspInstance &l, LpdTspSolution  &s, int tl)
/* Implemente esta função, entretanto, não altere sua assinatura */
{
    return naive(l, s, tl);
}

class subtourelim: public GRBCallback
{  
    const LpdTspInstance &l;
    Digraph::ArcMap<GRBVar> &y;
    double (GRBCallback::*solution_value)(GRBVar);
public:
    subtourelim(const LpdTspInstance &l, Digraph::ArcMap<GRBVar> &y) : l(l),y(y)  {    }
protected:
    void callback()
    { // --------------------------------------------------------------------------------
        //cout << "subtourelim PART 1" << endl;

    // get the correct function to obtain the values of the lp variables
        if  (where==GRB_CB_MIPSOL) { // if this condition is true, all variables are integer
            solution_value = &subtourelim::getSolution;
        }
        else if ((where==GRB_CB_MIPNODE) && (getIntInfo(GRB_CB_MIPNODE_STATUS)==GRB_OPTIMAL)) {// node with optimal fractional solution
            solution_value = &subtourelim::getNodeRel;
        }
        else {
            return; // return, as this code do not take advantage of the other options
        }
        // --------------------------------------------------------------------------------
        // Stores the edges with fractional values and integer values
        vector<Arc> FracEdges,OneEdges;
        // produces a subgraph h of g, with edges e with y[a]==1 
        // contracted, so we can apply Gomory-Hu tree in a small graph
        ArcBoolMap one_filter(l.g, false); // start without any edge
        ArcBoolMap non_zero_filter(l.g, false); // start without any edge
        for (ArcIt a(l.g); a != INVALID; ++a) {
            if ((this->*solution_value)(y[a]) > 1 - MY_EPS) {
                OneEdges.push_back(a); // stores the edges with y[a]==1
            }
            else if ((this->*solution_value)(y[a]) > MY_EPS) {
                FracEdges.push_back(a); // includes edges with 0 < y[a] < 1
            }
        }// define the subgraph with edges that have y[a]==1

        try {
            // --------------------------------------------------------------------------------
            // Use union-find to contract nodes (to obtain graph where each componente of g is contracted)
            //for (int i=0;i<l.n;i++) UFIndexToNode[i]=INVALID;
            DNodeIntMap aux_map(l.g);
            UnionFind<DNodeIntMap> UFNodes(aux_map);
            for (DNodeIt v(l.g); v!=INVALID; ++v) UFNodes.insert(v);
            for (vector<Arc>::iterator a_it=OneEdges.begin(); a_it != OneEdges.end(); ++a_it)
                UFNodes.join(l.g.source(*a_it),l.g.target(*a_it));// No problem if they are in a same component
            // --------------------------------------------------------------------------------
            // Put in a separate set all edges that are not inside a component 
            vector<Arc> CrossingEdges;
            for (ArcIt a(l.g); a != INVALID; ++a) 
                if (UFNodes.find(l.g.source(a)) != UFNodes.find(l.g.target(a)))
                    CrossingEdges.push_back(a);
            // --------------------------------------------------------------------------------
            // Generate an inverted list UFIndexToNode to find the node that represents a component
            vector<bool> ComponentIndex(l.n);
            vector<DNode> Index2h(l.n);
            for(int i=0;i<l.n;i++) ComponentIndex[i]=false;
            for (DNodeIt v(l.g); v!=INVALID; ++v) ComponentIndex[UFNodes.find(v)]=true;
            // --------------------------------------------------------------------------------
            // Generate graph of components, add one node for each component and edges
            Digraph h;
            DNodeValueMap h_node_names(h); int name = 1;
            ArcValueMap h_capacity(h); 
            for(int i=0;i<l.n;i++)  // add nodes to the graph h
                if (ComponentIndex[i]) {
                    Index2h[i] = h.addNode();
                    h_node_names[ Index2h[i] ] = name++;
                }
            for (vector<Arc>::iterator a_it=FracEdges.begin(); a_it != FracEdges.end(); ++a_it){
                DNode  u = l.g.source(*a_it),              v = l.g.target(*a_it),
                hu = Index2h[UFNodes.find(u)],   hv = Index2h[UFNodes.find(v)];
                Arc a = h.addArc(hu , hv );         // add edges to the graph h
                h_capacity[a] = (this->*solution_value)(y[*a_it]);
            }
            // --------------------------------------------------------------------------------

            if (CrossingEdges.size() > 0) {
                HaoOrlin<Digraph, ArcValueMap> min_cut(h,h_capacity);
                min_cut.run();

                DNodeBoolMap cutmap(h);
                min_cut.minCutMap(cutmap);

                //          1 -> 0       0 -> 1
                GRBLinExpr exprOut = 0, exprIn = 0;

                // Percorre as arestas que cruzam alguma componente e insere as que pertencem ao corte
                for (vector<Arc>::iterator a_it=CrossingEdges.begin();a_it!=CrossingEdges.end();++a_it){
                    DNode u=l.g.source(*a_it), v=l.g.target(*a_it),
                        hu = Index2h[UFNodes.find(u)], hv=Index2h[UFNodes.find(v)];
                    if (cutmap[hu] != cutmap[hv]) {
                        if (cutmap[hu]) // source is 1
                            exprOut += y[*a_it];
                        else // source is 0
                            exprIn += y[*a_it];
                    }
                }
                addLazy(exprOut >= 1);
                addLazy(exprIn >= 1);
            }

        } catch (...) {
            cout << "Error during callback..." << endl;
        }
    }
};


//------------------------------------------------------------------------------
bool exact(const LpdTspInstance &l, LpdTspSolution  &s, int tl)
/* Implemente esta função, entretanto, não altere sua assinatura */
{
    try {
        GRBEnv env = GRBEnv();
        GRBModel model = GRBModel(env);

#if GUROBI_NEWVERSION
        model.getEnv().set(GRB_IntParam_LazyConstraints, 1);

        int seed = 1;
        srand48(seed);
        model.getEnv().set(GRB_IntParam_Seed, seed);
#else
        model.getEnv().set(GRB_IntParam_DualReductions, 0); // Dual reductions must be disabled when using lazy constraints
#endif

        model.set(GRB_StringAttr_ModelName, "LPD-TSP"); // name to the problem
        model.set(GRB_IntAttr_ModelSense, GRB_MINIMIZE); // is a minimization problem

        Digraph::ArcMap<GRBVar> y(l.g);
        Digraph::ArcMap<GRBVar> d(l.g);
        Digraph::ArcMap<vector<GRBVar>> f(l.g);
        Digraph::NodeMap<GRBVar> x(l.g);

        for (ArcIt a(l.g); a!=INVALID; ++a) {
            vector<GRBVar> f_k(l.k);
            for (int k = 0; k < l.k; k++) {
                f_k[k] = model.addVar(0.0, l.capacity, 1.0, GRB_CONTINUOUS, "f_" + l.vname[l.g.source(a)] + "-" + l.vname[l.g.target(a)] + "_" + to_string(k+1) );
            }
            f[a] = f_k;

            y[a] = model.addVar(0.0, 1.0, l.weight[a], GRB_BINARY, "y_" + l.vname[l.g.source(a)] + "-" + l.vname[l.g.target(a)]);
            
            d[a] = model.addVar(0.0, 1.0, 1.0, GRB_BINARY, "d_" + l.vname[l.g.source(a)] + "-" + l.vname[l.g.target(a)]);
        }
        for (DNodeIt v(l.g); v!=INVALID; ++v) {
            x[v] = model.addVar(1, l.n, 1.0, GRB_INTEGER, "x_" + l.vname[v]);
        }
        model.update(); // run update to use model inserted variables

        GRBLinExpr exprObjective = 0;
        for (ArcIt a(l.g); a!=INVALID; ++a) {
            exprObjective += y[a] * l.weight[a];
        }
        model.setObjective(exprObjective, GRB_MINIMIZE);
        model.update();

        vector<bool> items_constr_added(l.k, false);
        model.addConstr(x[l.depot] == 1); 
        for (ArcIt a(l.g); a!=INVALID; ++a) {
            if (l.g.target(a) == l.depot)
                continue;

            DNode u = l.g.source(a);
            DNode v = l.g.target(a);

            model.addConstr(x[v] - x[u] + 10*l.n*(1-y[a]) >= y[a]);

            if (l.s[u] != 0 && !items_constr_added[ l.s[u]-1 ]) {
                for (DNodeIt vv(l.g); vv!=INVALID; ++vv) {
                    if (l.t[vv] == l.s[u]) {
                        model.addConstr(x[u] <= x[vv] + 1);
                        items_constr_added[ l.s[u]-1 ] = true;
                        break;
                    }
                }
            }
            if (l.s[v] != 0 && !items_constr_added[ l.s[v]-1 ]) {
                for (DNodeIt vv(l.g); vv!=INVALID; ++vv) {
                    if (l.t[vv] == l.s[v]) {
                        model.addConstr(x[v] <= x[vv] + 1);
                        items_constr_added[ l.s[v]-1 ] = true;
                        break;
                    }
                }
            }
        }

        // Add degree constraint for each node (sum of solution edges incident to a node is 2)
        for (DNodeIt v(l.g); v!=INVALID; ++v) {
            GRBLinExpr exprOut = 0, exprIn = 0;

            for (OutArcIt a(l.g, v); a!=INVALID; ++a)
                exprOut += y[a];
            model.addConstr(exprOut == 1);

            for (InArcIt a(l.g, v); a!=INVALID; ++a)
                exprIn += y[a];
            model.addConstr(exprIn == 1);
        }

        for (DNodeIt v(l.g); v!=INVALID; ++v) {
            for (int k = 0; k < l.k; k++) {
                GRBLinExpr exprOut = 0, exprIn = 0;

                for (OutArcIt a(l.g, v); a!=INVALID; ++a)
                    exprOut += f[a][k];
                
                for (InArcIt a(l.g, v); a!=INVALID; ++a)
                    exprIn += f[a][k];

                double demand = 0.0;
                if (l.s[v] == k+1) // is a pickup node of item k
                    demand = l.items[k].w;
                else if (l.t[v] == k+1) // is a delivery node of item k
                    demand = -( l.items[k].w );

                if (demand == 0.0) // nothing about this item on this node
                    continue;

                model.addConstr(exprOut - exprIn == demand);
            }
        }

        for (ArcIt a(l.g); a!=INVALID; ++a) {
            GRBLinExpr expr = 0;
            for (int k = 0; k < l.k; k++) {
                GRBLinExpr fak = f[a][k];
                model.addConstr(fak >= 0.0);

                expr += f[a][k];
            }
            model.addConstr(expr >= 0.0);
            model.addConstr(expr <= l.capacity * y[a]);
        }
    
        model.update(); // Process any pending model modifications.
        if (tl >= 0) 
            model.getEnv().set(GRB_DoubleParam_TimeLimit, tl);

        subtourelim cb = subtourelim(l, y);
        model.setCallback(&cb);
        
        naive(l, s, tl);
        if (s.cost < DBL_MAX) {
            model.getEnv().set(GRB_DoubleParam_Cutoff, s.cost + 0.1);
        }

        model.update(); // Process any pending model modifications.
        model.optimize();

        int status = model.get(GRB_IntAttr_Status);
        if (status == GRB_TIME_LIMIT) {
            s.upperBound = model.get(GRB_DoubleAttr_ObjVal);
            s.lowerBound = model.get(GRB_DoubleAttr_ObjBound);
        } else if (status == GRB_OPTIMAL) {
            s.cost = 0.0;

            DNode node = l.depot;
            s.tour.clear();
            s.tour.push_back(node);

            while (s.tour.size() != l.n) {
                for (OutArcIt a(l.g, node); a!=INVALID; ++a) {
                    if (BinaryIsOne(y[a].get(GRB_DoubleAttr_X))) {
                        s.cost += l.weight[a];

                        node = l.g.target(a);
                        s.tour.push_back(node);
                        break;
                    }
                }
            }

            for (OutArcIt a(l.g, s.tour.back()); a!=INVALID; ++a) 
                if (l.g.target(a) == l.depot)
                    s.cost += l.weight[a];
            
            s.upperBound = s.lowerBound = s.cost;   

            return true;
        }

    } catch (GRBException e) {
        cout << "Error number: " << e.getErrorCode() << endl;
        cout << "Error message: " << e.getMessage() << endl;
    } catch (...) {
        cout << "Error during optimization" << endl;
    }

    return false;

}