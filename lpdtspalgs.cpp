/*******************************************************************************
 * MC658 - Projeto e Análise de Algoritmos III - 2s2016
 * Prof.: Flavio Keidi Miyazawa
 * PED: Mauro Henrique Mulati
 ******************************************************************************/

/* IMPLEMENTE AS FUNCOES INDICADAS
 * DIGITE SEU RA: 123153
 * SUBMETA SOMENTE ESTE ARQUIVO */

#include <iostream>
#include <float.h>
#include <lemon/list_graph.h>
#include "mygraphlib.h"
#include "lpdtspalgs.h"

bool naive(const LpdTspInstance &l, LpdTspSolution  &s, int tl);


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
   return false;
}
//------------------------------------------------------------------------------
bool exact(const LpdTspInstance &l, LpdTspSolution  &s, int tl)
/* Implemente esta função, entretanto, não altere sua assinatura */
{
   return naive(l, s, tl);
}
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

