#ifndef CLAUSE_H
#define CLAUSE_H
#include <list>

using namespace std;

struct literal {
    int name;
    int flag = 0;  /// 0 when unassigned, level when true, -level when false
};

class Clause
{
    public:
        Clause();
        virtual ~Clause();
        int flag; /// 0 when unassigned, level when sat
        int nr_literals;
        int nr_literals_false;
        list<literal> lst;
    protected:
    private:
};

#endif // CLAUSE_H
