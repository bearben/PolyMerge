/*  vol.cpp
 *
 *  Copyright (C) 2016-2017 Cunjing Ge.
 *
 *  All rights reserved.
 *
 *  This file is part of VolCE.
 *  See COPYING for more information on using this software.
 */

#include "solver.h"
#include "glpk.h"
#include <stdio.h>

std::vector<z3::expr> 	x_expr;
std::vector<z3::expr> 	lc_expr;
std::vector<z3::expr>	wl_expr;
z3::context 			ctxt;

z3::expr z3mkconst(z3::context &c, const double val) {

	//real const
	char num[STRLEN];
	sprintf(num, "%.8g", val);
	//remove char '+'
	for (unsigned int i = 0; num[i] != 0; i++)
		if (num[i] == '+')
			while (num[i] != 0)
				num[i] = num[i + 1], i++;
	return c.real_val(num);
}

bool isle(int op, bool b)
{
	if ((op == 1 && b == 1) || (op == -10 && b == 0)){
		//GT
		return false;
	}else if ((op == 1 && b == 0) || (op == -10 && b == 1)){
		//LE
		return true;
	}else if ((op == 10 && b == 1) || (op == -1 && b == 0)){
		//GE
		return true;
	}else if ((op == 10 && b == 0) || (op == -1 && b == 1)){
		//LT
		return false;
	}else if (op == 0){
		assert(false);
	}
	assert(false);
}

bool array_same(int *a, int *b, unsigned int size)
{
	for (unsigned int i = 0; i < size; i++)
		if (a[i] != b[i])
			return false;
	return true;
}

/*
void printH(const std::vector<unsigned int> &hid, const std::vector<std::vector<double>> &A, 
				const std::vector<bool> &isle, const std::vector<double> &b)
{

	for (unsigned int i = 0; i < hid.size(); i++)
	{
		if (i < hid.size()) 
			std::cout << "h" << hid[i] << ": ";
		for (unsigned int j = 0; j < A[0].size(); j++)
			if (A[i][j] != 0)
			{
				if (A[i][j] == 1)
					std::cout << "x" << j << " ";
				else if (A[i][j] == -1)
					std::cout << "-x" << j << " ";
				else
					std::cout << A[i][j] << " * x" << j << " ";
			}
		if (isle[i]) std::cout << "<= ";
		else std::cout << " < ";
		
		std::cout << b[i] << std::endl;
	}
	
}
*/


void volce::solver::merge_init()
{

	// create smt expressions for z3
	for (unsigned int i = 0; i < nVars; i++)
	{
		char str[STRLEN];
		sprintf( str, "x%d", i );
		x_expr.push_back(ctxt.real_const(str));
	}

	for(unsigned int i = 0; i < nFormulas; i++){
	
		assert(bigop[i] != 0);
		
		//make first term
		z3::expr expr = ctxt.int_val(0);
		
		int cmp = bigop[i];
		if (cmp == 1){
			//GT			
			for (unsigned int j = 0; j < nVars; j++)
				if (bigA(i, j) != 0)
					expr = expr + z3mkconst(ctxt, -bigA(i, j)) * x_expr[j];
			
			expr = (expr < z3mkconst(ctxt, -bigb(i)));
		
			std::cout << "h" << i << ": ";
			for (unsigned int j = 0; j < nVars; j++)
			{
				double aij = -bigA(i, j);
				if (aij != 0)
				{
					if (aij == 1)
						std::cout << "x" << j << " ";
					else if (aij == -1)
						std::cout << "-x" << j << " ";
					else
						std::cout << aij << " * x" << j << " ";
				}
			}		
			std::cout << "< " << -bigb(i) << std::endl;
			
		}else if (cmp == -10){
			//LE
			for (unsigned int j = 0; j < nVars; j++)
				if (bigA(i, j) != 0)
					expr = expr + z3mkconst(ctxt, bigA(i, j)) * x_expr[j];
			
			expr = (expr <= z3mkconst(ctxt, bigb(i)));
			
			std::cout << "h" << i << ": ";
			for (unsigned int j = 0; j < nVars; j++)
			{
				double aij = bigA(i, j);
				if (aij != 0)
				{
					if (aij == 1)
						std::cout << "x" << j << " ";
					else if (aij == -1)
						std::cout << "-x" << j << " ";
					else
						std::cout << aij << " * x" << j << " ";
				}
			}		
			std::cout << "<= " << bigb(i) << std::endl;
			
		}else if (cmp == 10){
			//GE
			for (unsigned int j = 0; j < nVars; j++)
				if (bigA(i, j) != 0)
					expr = expr + z3mkconst(ctxt, -bigA(i, j)) * x_expr[j];
			
			expr = (expr <= z3mkconst(ctxt, -bigb(i)));
			
			std::cout << "h" << i << ": ";
			for (unsigned int j = 0; j < nVars; j++)
			{
				double aij = -bigA(i, j);
				if (aij != 0)
				{
					if (aij == 1)
						std::cout << "x" << j << " ";
					else if (aij == -1)
						std::cout << "-x" << j << " ";
					else
						std::cout << aij << " * x" << j << " ";
				}
			}		
			std::cout << "<= " << -bigb(i) << std::endl;
			
		}else if (cmp == -1){
			//LT
			for (unsigned int j = 0; j < nVars; j++)
				if (bigA(i, j) != 0)
					expr = expr + z3mkconst(ctxt, bigA(i, j)) * x_expr[j];
			
			expr = (expr < z3mkconst(ctxt, bigb(i)));
			
			std::cout << "h" << i << ": ";
			for (unsigned int j = 0; j < nVars; j++)
			{
				double aij = bigA(i, j);
				if (aij != 0)
				{
					if (aij == 1)
						std::cout << "x" << j << " ";
					else if (aij == -1)
						std::cout << "-x" << j << " ";
					else
						std::cout << aij << " * x" << j << " ";
				}
			}		
			std::cout << "< " << bigb(i) << std::endl;
			
		}else if (cmp == 0){
			assert(false);
		}
	
		lc_expr.push_back(expr.simplify());
	}
	
	//add boundaries
	//Disable bounds when wordlength == 0
	if (wordlength > 0){
		for(unsigned int i = 0; i < nVars; i++){
			//Xi <= 2^(wordlength-1) - 1;
			z3::expr expr1 = (x_expr[i] <= z3mkconst(ctxt, pow(2, wordlength - 1) - 1));
			wl_expr.push_back(expr1);
			
			//-Xi <= 2^(wordlength-1)
			z3::expr expr2 = (-x_expr[i] <= z3mkconst(ctxt, pow(2, wordlength - 1)));
			wl_expr.push_back(expr2);
		}
	}

}

void volce::solver::redundancy_removal(int *bools, z3::solver &z3solver)
{

	//std::vector<int> vars;
	
	std::vector<unsigned int> hid;
	std::vector<unsigned int> rmhid;
	
	for(unsigned int i = 0; i < nFormulas; i++)
		if (bools[i] >= 0)
			hid.push_back(i);
			
	unsigned int i = 0;
	while (i < hid.size())
	{
		
		z3solver.push();
		
		for (unsigned int j = 0; j < hid.size(); j++)
		{
			z3::expr term = lc_expr[hid[j]];
			if (bools[hid[j]] == 0)
				term = !term;
			if (i == j)
				term = !term;
			z3solver.add(term);
		}
		
		//std::cout << z3solver.to_smt2() << std::endl;
	
		if (z3solver.check() == z3::unsat)
		{
			//std::cout << "h" << hid[i] << " is redundant." << std::endl;
			rmhid.push_back(hid[i]);
			hid.erase(hid.begin() + i);
		}
		else
		{
			//std::cout << "h" << hid[i] << " is not redundant." << std::endl;
			i++;
		}
		
		z3solver.pop();
	}
			
	for (unsigned int i = 0; i < rmhid.size(); i++)
		bools[rmhid[i]] = -1;

	std::cout << "[R] Removed " << rmhid.size() << "/" << rmhid.size() + hid.size() << " redundant LCs." << std::endl;
}


void volce::solver::redundancy_removal_all()
{

	z3::solver z3solver(ctxt);
	for (unsigned int j = 0; j < wl_expr.size(); j++)
		z3solver.add(wl_expr[j]);

	for (unsigned int i = 0; i < bsols.size(); i++)
	{
		
		//std::cout << i << " ";
		redundancy_removal(bsols[i], z3solver);
		
		std::cout << "H" << i << " * " << multiplier[i] << ": ";
		for (unsigned int j = 0; j < nFormulas; j++)
			if (bsols[i][j] >= 0)
				std::cout << "h" << j << "(" << bsols[i][j] << ") ";
		std::cout << std::endl;
	}
	std::cout << std::endl;
		
}

void volce::solver::merge_all()
{

	// init z3 solver
	z3::solver z3solver(ctxt);
	for (unsigned int j = 0; j < wl_expr.size(); j++)
		z3solver.add(wl_expr[j]);
	
	// merge
	std::vector<int*> K;
	
	for (unsigned int i = 0; i < bsols.size(); i++)
	{
		int *ha = new int[nFormulas + 1];
		for (unsigned int j = 0; j < nFormulas; j++)
			ha[j] = bsols[i][j];
		ha[nFormulas] = multiplier[i];
		delete bsols[i];
		
		std::cout << "Merge H" << i << " with K (|K|=" << K.size() << ")" << std::endl;
		
		K = merge_set(ha, K, z3solver);
	}
	std::cout << std::endl;
	
	// process merged results
	multiplier.clear();
	bsols.clear();
	for (unsigned int i = 0; i < K.size(); i++)
	{
		int *ha = new int[nFormulas];
		for (unsigned int j = 0; j < nFormulas; j++)
			ha[j] = K[i][j];	

		multiplier.push_back(K[i][nFormulas]);
		bsols.push_back(ha);

		delete K[i];
	}
}

std::vector<int*> volce::solver::merge_set(int *ha, std::vector<int*> &K, z3::solver &z3solver)
{

/*
	std::cout << "Merge HA and K(" << K.size() << ")" << std::endl;
	std::cout << "HA: ";
	for (unsigned int i = 0; i < nFormulas; i++)
		if (ha[i] >= 0)
			std::cout << "h" << i << "(" << ha[i] << ") ";
	std::cout << std::endl;
	for (unsigned int k = 0; k < K.size(); k++)
	{
		std::cout << "K" << k << ": ";
		for (unsigned int i = 0; i < nFormulas; i++)
			if (K[k][i] >= 0)
				std::cout << "h" << i << "(" << K[k][i] << ") ";
		std::cout << std::endl;
	}
	std::cout << std::endl;
*/
	std::vector<int*> newK;
	
	for (unsigned int i = 0; i < K.size(); i++)
	{
		
		int *hb = K[i];
		
		if (array_same(ha, hb, nFormulas))
		{
			hb[nFormulas] += ha[nFormulas];
			
			for (unsigned int j = 0; j < K.size(); j++) 
				newK.push_back(K[j]);
			return newK;
		}
		
		if (ha[nFormulas] != hb[nFormulas])
			continue;
	
		int *hc = merge_AB(ha, hb, z3solver);
			
		if (hc[nFormulas] > 0)
		{
			delete ha;
			delete K[i];
		
			//for (unsigned int j = 0; j < nFormulas + 1; j++)
				//std::cout << hc[j] << " ";
			//std::cout << std::endl << std::endl;
			
			std::cout << "[M] Found two mergeable polytopes." << std::endl;
			
			redundancy_removal(hc, z3solver);
			
			for (unsigned int j = 0; j < K.size(); j++)
				if (i != j) newK.push_back(K[j]);
			return merge_set(hc, newK, z3solver);
		}
		else
		{
			delete hc;
		}
	}

	for (unsigned int i = 0; i < K.size(); i++) 
		newK.push_back(K[i]);
	newK.push_back(ha);
	return newK;

}

int* volce::solver::merge_AB(int* ha, int* hb, z3::solver &z3solver)
{

	int *hc = new int[nFormulas + 1];
	for (unsigned int i = 0; i < nFormulas + 1; i++) 
		hc[i] = -1;
	
	std::vector<unsigned int> haplus, haminus, hbplus, hbminus;
	
	z3::expr ha_expr = ctxt.bool_val(true);
	for (unsigned int i = 0; i < nFormulas; i++)
	{
		if (ha[i] == 1)
			ha_expr = ha_expr && lc_expr[i];
		else if (ha[i] == 0)
			ha_expr = ha_expr && !lc_expr[i];
	}
	ha_expr.simplify();
	
	z3::expr hb_expr = ctxt.bool_val(true);
	for (unsigned int i = 0; i < nFormulas; i++)
	{
		if (hb[i] == 1)
			hb_expr = hb_expr && lc_expr[i];
		else if (hb[i] == 0)
			hb_expr = hb_expr && !lc_expr[i];
	}
	hb_expr.simplify();
	
	//z3solver.push();
	//z3solver.add(ha_expr);
	//std::cout << "TEST A " << (z3solver.check() == z3::unsat) << std::endl;
	//z3solver.pop();
	//z3solver.push();
	//z3solver.add(hb_expr);
	//std::cout << "TEST B " << (z3solver.check() == z3::unsat) << std::endl;
	//assert(z3solver.check() == z3::unsat);		
	//z3solver.pop();
	
	unsigned int ia = 0;
	unsigned int ib = 0;
	int aisle = -1;
	int bisle = -1;
	while (ia < nFormulas || ib < nFormulas)
	{
		while (ia < nFormulas && ha[ia] < 0) ia++;
		if (ia < nFormulas)
		{			
			z3solver.push();
			z3solver.add(hb_expr);
			if (ha[ia] == 1)
				z3solver.add(!lc_expr[ia]);
			else
				z3solver.add(lc_expr[ia]);
			bool empty = z3solver.check() == z3::unsat;
			z3solver.pop();
			
			if (empty)
				haplus.push_back(ia);
			else
			{
				haminus.push_back(ia);
				bool flag = isle(bigop[ia], ha[ia]);
				//std::cout << "a" << flag << " " << bigop[ia] << " " << ha[ia] << std::endl;
				if (aisle < 0)
					aisle = flag;
				else if (aisle != flag)
					return hc;
			}
			
			ia++;
		}
		
		while (ib < nFormulas && hb[ib] < 0) ib++;
		if (ib < nFormulas)
		{			
			z3solver.push();
			z3solver.add(ha_expr);
			if (hb[ib] == 1)
				z3solver.add(!lc_expr[ib]);
			else
				z3solver.add(lc_expr[ib]);
			bool empty = z3solver.check() == z3::unsat;
			z3solver.pop();
			
			if (empty)
				hbplus.push_back(ib);
			else
			{
				hbminus.push_back(ib);
				bool flag = isle(bigop[ib], hb[ib]);
				//std::cout << "b" << flag << " " << bigop[ib] << " " << hb[ib] << std::endl;
				if (bisle < 0)
					bisle = flag;
				else if (bisle != flag)
					return hc;
			}
				
			ib++;
		}
		
		if (aisle >= 0 && bisle >= 0 && aisle == bisle)
			return hc;

	}
/*	
	std::cout << "HA+: ";
	for (unsigned int i = 0; i < haplus.size(); i++)
		std::cout << "h" << haplus[i] << "(" << ha[haplus[i]] << ") ";
	std::cout << std::endl;

	std::cout << "HA-: ";
	for (unsigned int i = 0; i < haminus.size(); i++)
		std::cout << "h" << haminus[i] << "(" << ha[haminus[i]] << ") ";
	std::cout << std::endl;
		
	std::cout << "HB+: ";
	for (unsigned int i = 0; i < hbplus.size(); i++)
		std::cout << "h" << hbplus[i] << "(" << hb[hbplus[i]] << ") ";
	std::cout << std::endl;

	std::cout << "HB-: ";
	for (unsigned int i = 0; i < hbminus.size(); i++)
		std::cout << "h" << hbminus[i] << "(" << hb[hbminus[i]] << ") ";
	std::cout << std::endl;
*/
	z3solver.push();
	z3solver.add(!ha_expr);
	z3solver.add(!hb_expr);
	for (unsigned int i = 0; i < haplus.size(); i++)
	{
		unsigned int id = haplus[i];
		if (ha[id] == 1)
			z3solver.add(lc_expr[id]);
		else if (ha[id] == 0)
			z3solver.add(!lc_expr[id]);
	}
	for (unsigned int i = 0; i < hbplus.size(); i++)
	{
		unsigned int id = hbplus[i];
		if (hb[id] == 1)
			z3solver.add(lc_expr[id]);
		else if (hb[id] == 0)
			z3solver.add(!lc_expr[id]);
	}
	bool empty = z3solver.check() == z3::sat;
	z3solver.pop();
	
	if (empty) return hc;
	
	for (unsigned int i = 0; i < haplus.size(); i++)
		hc[haplus[i]] = ha[haplus[i]];
	for (unsigned int i = 0; i < hbplus.size(); i++)
		hc[hbplus[i]] = hb[hbplus[i]];
	assert(ha[nFormulas] == hb[nFormulas]);
	hc[nFormulas] = ha[nFormulas];

	return hc;

}



