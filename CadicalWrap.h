/*************************************************************************************[PbSolver.cc]
UWrMaxSat based on KP-MiniSat+ -- Copyright (c) 2019-2020 Marek Piotrów

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef CadicalWrap_h
#define CadicalWrap_h

#include "cadical.hpp"
#include "mtl/Vec.h"
#include "core/SolverTypes.h"

namespace Minisat {

class SimpSolver {
protected:
    CaDiCaL::Solver *solver;
private:
    int nvars, nclauses, old_verbosity;
    bool firstCall;

    int lit2val(Lit p) {
        return sign(p) ? -var(p)-1 : var(p)+1;
    }

public:
    vec<Lit> conflict;
    int verbosity;
    uint64_t conflicts;

    SimpSolver() : nvars(0), nclauses(0), firstCall(true), conflicts(0) {
        solver = new CaDiCaL::Solver;
        verbosity = old_verbosity = solver->get("verbose");
    }
    ~SimpSolver() { delete solver; }

    Var newVar(bool polarity = true, bool dvar = true) {
        (void)polarity; (void)dvar;
        Var v = nvars++;
        solver->reserve((int)(v+1));
        return v;
    }
    int  nVars() const { return nvars; }
    int  nClauses() const { return nclauses; }
    void setPolarity(Var, bool) { /* unsupported */ }
    void setFrozen(Var , bool ) { /* not needed */ }

    bool addClause(const vec<Lit>& cl) {
        for (int i = 0; i < cl.size(); i++) solver->add(lit2val(cl[i]));
        solver->add(0); nclauses++; return true;
    }
    bool addEmptyClause() { 
        solver->add(0); nclauses++; return true; }
    bool addClause(Lit p) { 
        solver->add(lit2val(p)); solver->add(0); nclauses++; return true; }
    bool addClause(Lit p, Lit q) { 
        solver->add(lit2val(p)); solver->add(lit2val(q)); solver->add(0); nclauses++; return true; }
    bool addClause(Lit p, Lit q, Lit r) { 
        solver->add(lit2val(p)); solver->add(lit2val(q)); solver->add(lit2val(r)); solver->add(0);
        nclauses++; return true; }
    bool addClause_(vec<Lit>& cl) { return addClause(cl); }

    bool okay() { return solver->state() & CaDiCaL::VALID; }

    void interrupt() { solver->terminate(); }
    void clearInterrupt() { }

    void setConfBudget(int x) { solver->limit("conflicts", x); }
    void budgetOff() { solver->limit("conflicts", -1); }

    lbool solveLimited() {
        if (firstCall) {
            firstCall = false; printf("c Using %s SAT solver by Armin Biere (2020)\n", solver->signature()); }
        if (verbosity < 0) verbosity = 0; else if (verbosity > 3) verbosity = 3;
        if (verbosity != old_verbosity) solver->set("verbose", old_verbosity = verbosity);

        int ret = solver->solve();
        conflicts = solver->conflicts();
        return ret == 10 ? l_True : (ret == 20 ? l_False : l_Undef);
    }
    bool solve() {
        budgetOff();
        lbool ret = solveLimited();
        assert(ret != l_Undef);
        return ret == l_True;
    }
    lbool solveLimited(const vec<Lit>& assumps) {
        for (int i = 0; i < assumps.size(); i++)
            if (toInt(assumps[i]) >= 0) solver->assume(lit2val(assumps[i]));
        lbool ret = solveLimited();
        if (ret == l_False) {
            conflict.clear();
            for (int i = 0; i < assumps.size(); i++)
                if (toInt(assumps[i]) >= 0 && solver->failed(lit2val(assumps[i]))) conflict.push(~assumps[i]);
        }
        return ret;
    }
    bool solve(const vec<Lit>& assumps) {
        budgetOff();
        lbool ret = solveLimited(assumps);
        assert(ret != l_Undef);
        return ret == l_True;
    }
    bool eliminate(bool) { return solver->simplify() != 20; }
    bool isEliminated(Var) { /* not needed */ return false; }

    lbool value(Var v) const {
        int val = solver->fixed(v+1);
        return val == 0 ? l_Undef : (val > 0 ? l_True : l_False);
    }
    lbool value(Lit p) const {
        lbool val = value(var(p));
        if (sign(p)) 
            if (val == l_True) val = l_False; else if (val == l_False) val = l_True;
        return val;
    }

    lbool modelValue(Var v) const {
        int val = solver->val(v+1);
        return val == 0 ? l_Undef : (val > 0 ? l_True : l_False);
    }
    lbool modelValue(Lit p) const {
        lbool val = modelValue(var(p));
        if (sign(p)) 
            if (val == l_True) val = l_False; else if (val == l_False) val = l_True;
        return val;
    }

    void toDimacs(const char *file) { solver->write_dimacs(file); }
    void statistics() { solver->statistics(); }
};

}

#endif
