#include <fstream>
#include <list>
#include "Clause.h"
#include <map>
#include <cstdlib>
#include "Formula.h"
using namespace std;

ifstream f ("input.in");
ofstream g ("output.out");

int variables, clauses;

void read(int &variables, int &clauses, Formula &formula) {
    for(int i=1;i<=variables;i++) {
        formula.var_app[i] = 0;
        formula.var_app[(-1)*i] = 0;
    }
    int x;
    f>>variables>>clauses;
    for(int i=0;i<clauses;i++) {
        Clause cls;
        int nr = 0;
        do {
            f>>x;
            literal lit;
            lit.name = x;
            if(x!=0) {
                cls.lst.push_back(lit);
                formula.var_app[x]++;
                nr++;
            }
        }while(x!=0);
        cls.nr_literals = nr;
        formula.clauses.push_back(cls);
    }
}

void print_formula(Formula formula) {
    for(auto& clause:formula.clauses) {
        g<<clause.flag<<' '<<clause.nr_literals<<' ';
        //if(clause.flag == 0) {
            for(auto& literal: clause.lst)
                //if(literal.flag == 0)
                    g<<literal.name<<' '<<literal.flag<<' ';
            g<<'\n';
        //}
    }
}

int find_unit_clause(Formula formula) {

    for(auto& clause: formula.clauses)
        if(clause.flag == 0 && clause.nr_literals - clause.nr_literals_false == 1)
            for(auto& lit: clause.lst) {
                if(lit.flag == 0)
                    return lit.name;
            }
    return false;
}

int find_pure_literal(Formula formula) {
    for(int i=1;i<=variables;i++) {
        if(formula.var_app[i] > 0 && formula.var_app[(-1)*i] == 0)
            return i;
        else
            if(formula.var_app[(-1)*i] > 0 && formula.var_app[i] == 0)
                return (-1)*i;
    }
    return 0;
}

void unit_propagate(Formula &formula, int unit_literal, int changes) {
    /// search for the literal in each clause
    /// delete clauses that contain the literal
    /// delete the negated literal
    formula.var_app[unit_literal] = 0;
    formula.var_app[(-1)*unit_literal] = 0;

    for(auto& clause: formula.clauses) {
        if(clause.flag == 0)
            for(auto& lit: clause.lst) {
                if(lit.flag == 0 && lit.name == (-1)*unit_literal) {
                    //var_app[lit.name]--;
                    lit.flag = (-1)*changes;
                    clause.nr_literals_false++;
                }
                else if(lit.flag == 0 && lit.name == unit_literal){
                    lit.flag = changes;
                    clause.flag = changes;
                    for(auto& lit2: clause.lst)
                        if(lit2.name != unit_literal && lit2.flag == 0){
                            formula.var_app[lit2.name]--;
                            lit2.flag = changes;
                        }
                }
        }
    }
}

void pure_literal(Formula &formula, int pure_lit, int changes) {
    /// delete clauses that contain the literal
    formula.var_app[pure_lit] = 0;
    for(auto& clause: formula.clauses) {
        if(clause.flag == 0)
            for(auto& lit: clause.lst) {
                if(lit.flag == 0 && lit.name == pure_lit){
                    lit.flag = changes;
                    clause.flag = changes;
                    for(auto& lit2: clause.lst)
                        if(lit2.name != pure_lit && lit2.flag == 0) {
                            formula.var_app[lit2.name]--;
                            lit2.flag = changes;
                        }
                }
            }
    }
}

bool empty_clause (Formula formula) {
    for(auto& clause: formula.clauses) {
        if(clause.flag == 0 && clause.nr_literals == clause.nr_literals_false)
            return true;
    }
    return false;
}

bool empty_formula(Formula formula) {
    for(auto& clause: formula.clauses)
        if(clause.flag == 0)
            return false;
    return true;
}

int find_most_popular_lit(Formula formula) {

    int maxi = -1, lit=0;
    for(int i=1;i<=variables;i++) {
        if(formula.var_app[i] > maxi || formula.var_app[(-1)*i] > maxi) {
            maxi = formula.var_app[i];
            lit = i;
        }
    }
    if(lit!=0)
        return lit;
    else
        return 0;
}

int find_first_lit (Formula formula) {

    for(auto& cls: formula.clauses)
        if(cls.flag == 0)
            for(auto& lit: cls.lst)
                if(lit.flag == 0)
                    return lit.name;
}

void print_assignment(list<int> assignment) {

    int v[variables+1];
    for(int i=1;i<=variables;i++)
        v[i] = 0;
    int nr=1;
    for(auto& lit: assignment) {
        g<<lit<<' ';
        if(nr++ % 10 == 0) g<<'\n';
        v[abs(lit)] = 1;
    }
    for(int i=1;i<=variables;i++)
        if(v[i] == 0) {
            g<<i<<' ';
            if(nr++ % 10 == 0) g<<'\n';
        }
    g<<'\n';
}

void revert (Formula &formula, list<int> assignment,int level) {

    for(auto& clause:formula.clauses) {
        for(auto& l: clause.lst)
            if(l.flag == level || l.flag == level*(-1)) {
                if(l.flag < 0)
                    clause.nr_literals_false--;
                l.flag = 0;
                formula.var_app[l.name]++;
            }
        if(clause.flag == level)
            clause.flag = 0;
    }
}

bool dpll (Formula formula, list<int> assignment, int level) {

    int lit = 0;

    while(lit = find_unit_clause(formula)) {

        assignment.push_back(lit);
        unit_propagate(formula, lit, level);
        //g<<"Unit propagation on: "<<lit<<'\n';
        //print_formula(formula);
        //g<<"var app: ";
        //for(int i=0;i<=variables;i++)
        //    g<<i<<' '<<formula.var_app[i]<<' '<<formula.var_app[(-1)*i]<<'\n';
        if(empty_clause(formula))
            return false;
    }

    while(lit = find_pure_literal(formula)) {

        assignment.push_back(lit);
        pure_literal(formula,lit, level);
        //g<<"Pure literal: "<<lit<<'\n';
        //print_formula(formula);
        //g<<"var app: ";
        //for(int i=0;i<=variables;i++)
        //    g<<i<<' '<<formula.var_app[i]<<' '<<formula.var_app[(-1)*i]<<'\n';
        if(empty_clause(formula))
            return false;
    }

    if(empty_formula(formula)) {
        g<<"SAT\n";
        print_assignment(assignment);
        return true;
    }


    lit = find_most_popular_lit(formula);
    //lit = find_first_lit(formula);
    //g<<lit<<'\n';

    literal l;
    l.name = lit;
    Clause cls;
    cls.lst = {l};
    cls.nr_literals = 1;
    formula.clauses.push_back(cls);
    formula.var_app[lit]++;

    //g<<"Split on: "<<l.name<<'\n';
    if(dpll(formula,assignment,level+1))
        return true;
    formula.clauses.pop_back();
    revert(formula,assignment,level+1);
    l.name = l.name*(-1);
    l.flag = 0;
    cls.lst = {l};
    cls.nr_literals = 1;
    formula.clauses.push_back(cls);
    formula.var_app[lit]++;
    //g<<"Split on: "<<l.name<<'\n';
    if(dpll(formula,assignment,level+1))
        return true;
    formula.clauses.pop_back();
    revert(formula,assignment,level+1);

    /*
    formula = unit_propagate(formula,lit,level+1);
    //g<<"Split on: "<<lit<<'\n';
    //print_formula(formula);
    //g<<"var app: ";
    //for(int i=0;i<=variables;i++)
    //        g<<i<<' '<<var_app[i]<<' '<<var_app[(-1)*i]<<'\n';
    if(dpll(formula,assignment,level+1))
        return true;
    formula = revert(formula,assignment,level+1);

    formula = unit_propagate(formula,lit*(-1),level+1);
    //g<<"Split on: "<<lit*(-1)<<'\n';
    //print_formula(formula);
    //g<<"var app: ";
    //    for(int i=0;i<=variables;i++)
    //        g<<i<<' '<<var_app[i]<<' '<<var_app[(-1)*i]<<'\n';
    if(dpll(formula,assignment,level+1))
        return true;
    formula = revert(formula,assignment,level+1);

    */
    return false;
}

int main()
{
    Formula formula;
    read(variables, clauses, formula);
    //print_formula(formula);
    int nr = 0;
    if(!dpll(formula,{},1)) g<<"UNSAT\n";

    /*
    int level = 1;
    print_formula(formula);
    for(int i=0;i<=variables;i++)
        g<<i<<' '<<formula.var_app[i]<<' '<<formula.var_app[(-1)*i]<<'\n';
    g<<'\n';
    unit_propagate(formula, 1, 1);
    print_formula(formula);
    for(int i=0;i<=variables;i++)
        g<<i<<' '<<formula.var_app[i]<<' '<<formula.var_app[(-1)*i]<<'\n';
    g<<'\n';
    revert(formula,{},1);
    print_formula(formula);
    g<<'\n';
    for(int i=0;i<=variables;i++)
        g<<i<<' '<<formula.var_app[i]<<' '<<formula.var_app[(-1)*i]<<'\n';

    */
    return 0;
}
