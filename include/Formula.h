#ifndef FORMULA_H
#define FORMULA_H
#include "Clause.h"
#include <map>
using namespace std;
class Formula
{
    public:
        Formula();
        virtual ~Formula();
        list<Clause> clauses;
        map<int, int> var_app;
    protected:
    private:
};

#endif // FORMULA_H
