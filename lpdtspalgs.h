/*******************************************************************************
 * MC658 - Projeto e Análise de Algoritmos III - 2s2016
 * Prof.: Flavio Keidi Miyazawa
 * PED: Mauro Henrique Mulati
 ******************************************************************************/

/* Atenção: Qualquer alteração neste arquivo não terá efeito no projeto a ser 
 * testado no momento da avaliação. */

#ifndef LPDTSPALGS_H
#define LPDTSPALGS_H

#include "lpdtsp.h"

bool constrHeur(const LpdTspInstance &l, LpdTspSolution  &s, int tl);
bool metaHeur(const LpdTspInstance &l, LpdTspSolution  &s, int tl);
bool exact(const LpdTspInstance &l, LpdTspSolution  &s, int tl);

#endif
