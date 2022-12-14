/****************************************************************************[Hardware_clausify.cc]
Copyright (c) 2005-2010, Niklas Een, Niklas Sorensson

KP-MiniSat+ based on MiniSat+ -- Copyright (c) 2018-2020 Michał Karpiński, Marek Piotrów

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

#include "Hardware.h"
#include "FEnv.h"
#include "MsSolver.h"

struct Clausifier
{
    SimpSolver&  s;
    Minisat::vec<Lit> tmp_clause;
    vec<Formula> tmp_marked;

    Clausifier(SimpSolver& _s) : s(_s) {}

    static /*WARNING*/ CMap<int>      occ;
    static /*WARNING*/ CMap<Var>      vmap;
    static /*WARNING*/ CMap<Lit,true> vmapp;
    FMap<bool,true>   seen;

    inline void clause(Lit a, Lit b) {
        tmp_clause.clear(); tmp_clause.push(a); tmp_clause.push(b); s.addClause(tmp_clause); }
    inline void clause(Lit a, Lit b, Lit c) {
        tmp_clause.clear(); tmp_clause.push(a); tmp_clause.push(b); tmp_clause.push(c); s.addClause(tmp_clause); }
    inline void clause(Lit a, Lit b, Lit c, Lit d) {
        tmp_clause.clear(); tmp_clause.push(a); tmp_clause.push(b); tmp_clause.push(c); tmp_clause.push(d); s.addClause(tmp_clause); }


    void  usage  (Formula f);
    void _collect(Formula f, vec<Formula>& out);
    void  collect(Formula f, vec<Formula>& out);

    Lit   basicClausify   (Formula f);
    Lit   polarityClausify(Formula f);
};

CMap<int>      Clausifier::occ  (0);
CMap<Var>      Clausifier::vmap (var_Undef);
CMap<Lit,true> Clausifier::vmapp(lit_Undef);

void clear_clausifier_static_maps() {
    Clausifier::occ.clear(); Clausifier::vmap.clear(); Clausifier::vmapp.clear();
}

void Clausifier::usage(Formula f)
{
    if (Atom_p(f))
        return;

    occ.set(f,occ.at(f)+1);

    if (occ.at(f) == 1){
        if (Bin_p(f)){
            usage(left(f)); usage(right(f));
        }else if (ITE_p(f)){
            usage(cond(f)); usage(tt(f)); usage(ff(f));
        }else{
            assert(FA_p(f));
            usage(FA_x(f)); usage(FA_y(f)); usage(FA_c(f));
        }
    }
}

void Clausifier::collect(Formula f, vec<Formula>& out)
{
    tmp_marked.clear();
    _collect(left(f), out);
    _collect(right(f),out);
    for (int i = 0; i < tmp_marked.size(); i++)
        seen.set(tmp_marked[i],false);
}

void Clausifier::_collect(Formula f, vec<Formula>& out)
{
    if (!seen.at(f)){
        seen.set(f,true);
        tmp_marked.push(f);
        if (Bin_p(f) && op(f) == op_And && !sign(f) && occ.at(f) == 1){
            _collect(left(f) ,out);
            _collect(right(f),out);
        }
        else
            out.push(f);
    }
}

Lit Clausifier::polarityClausify(Formula f)
{
    Lit result = lit_Undef;

    if (Atom_p(f)){
      #if 0
        assert(!Const_p(f));
      #else
        if (Const_p(f)){
            Var x = s.newVar();
            s.addClause(mkLit(x, (f == _0_)));
            result = mkLit(x);
        }else
      #endif
        result = mkLit(index(f),sign(f));
    }else if (vmapp.at(f) != lit_Undef && !s.isEliminated(var(vmapp.at(f)))){
        result = vmapp.at(f);
    }else{
#ifdef MINISAT
        result = vmapp.at(~f) != lit_Undef && !s.isEliminated(var(vmapp.at(~f))) ?
            mkLit(var(vmapp.at(~f))) : mkLit(s.newVar(l_Undef, !opt_branch_pbvars));
#elif 1
        result = vmapp.at(~f) != lit_Undef && !s.isEliminated(var(vmapp.at(~f))) ?
            mkLit(var(vmapp.at(~f))) : mkLit(s.newVar(true /*l_Undef*/, !opt_branch_pbvars));
#else
        result = mkLit(s.newVar(l_Undef, !opt_branch_pbvars));
#endif
        if (Bin_p(f)){
            if (op(f) == op_And){
                vec<Formula> conj;
                collect(f, conj);
                assert(conj.size() > 1);
                if (!sign(f)){
                    for (int i = 0; i < conj.size(); i++)
                        if (Bin_p(conj[i]) && op(conj[i]) == op_And && sign(conj[i]) && occ.at(conj[i]) == 1 &&
                                vmapp.at(conj[i]) == lit_Undef && vmapp.at(~conj[i]) == lit_Undef) {
                            vec<Formula> disj;
                            collect(conj[i], disj);
                            Minisat::vec<Lit> ls;
                            ls.push(~result);
                            for (int j = 0; j < disj.size(); j++)
                                ls.push(polarityClausify(~disj[j]));
                            s.addClause(ls);
                        } else 
                            clause(~result,polarityClausify(conj[i]));
                }else{
                    Minisat::vec<Lit> ls;
                    ls.push(result);
                    for (int i = 0; i < conj.size(); i++)
                        ls.push(polarityClausify(~conj[i]));
                    s.addClause(ls);
                }
                //printf("and: %d = ", var(result));
                //for (int i = 0; i < conj.size(); i++)
                //    printf("%c%d ", sign(polarityClausify(conj[i])) ? '-' : ' ',
                //           var(polarityClausify(conj[i])));
                //printf("\n");
            }else{
                Lit l  = polarityClausify( left (f));
                Lit r  = polarityClausify( right(f));
                Lit nl = polarityClausify(~left (f));
                Lit nr = polarityClausify(~right(f));

                //printf("equiv:\n");
                assert(op(f) == op_Equiv);
                if (!sign(f)){
                    clause(~result, nl,  r);
                    clause(~result,  l, nr);
                }else{
                    clause( result, nl, nr);
                    clause( result,  l,  r);
                }
            }
        }else if (ITE_p(f)){
            Lit  c = polarityClausify( cond(f));
            Lit nc = polarityClausify(~cond(f));

            if (!sign(f)){
                Lit  a = polarityClausify( tt  (f));
                Lit  b = polarityClausify( ff  (f));
                clause(~result, nc,  a);
                clause(~result,  c,  b);
                clause( a,  b, ~result);
            }else{
                Lit na = polarityClausify(~tt  (f));
                Lit nb = polarityClausify(~ff  (f));
                clause( result, nc, na);
                clause( result,  c, nb);
                clause(na, nb,  result);
            }
        }else{
            assert(FA_p(f));
            if (isCarry(f)){
                //printf("carry:\n");
                if (!sign(f)){
                    Lit  a = polarityClausify( FA_x(f));
                    Lit  b = polarityClausify( FA_y(f));
                    Lit  c = polarityClausify( FA_c(f));
                    clause(~result,  a,  b);
                    clause(~result,  c,  a);
                    clause(~result,  c,  b);
                }else{
                    Lit na = polarityClausify(~FA_x(f));
                    Lit nb = polarityClausify(~FA_y(f));
                    Lit nc = polarityClausify(~FA_c(f));
                    clause( result, na, nb);
                    clause( result, nc, na);
                    clause( result, nc, nb);
                }
            }else{
                Lit  a = polarityClausify( FA_x(f));
                Lit  b = polarityClausify( FA_y(f));
                Lit  c = polarityClausify( FA_c(f));
                Lit na = polarityClausify(~FA_x(f));
                Lit nb = polarityClausify(~FA_y(f));
                Lit nc = polarityClausify(~FA_c(f));

                //printf("sum:\n");
                if (!sign(f)){
                    clause(~result, nc,  na,  b);
                    clause(~result, nc,   a, nb);
                    clause(~result,  c,  na, nb);
                    clause(~result,  c,   a,  b);
                }else{
                    clause( result, nc,  na, nb);
                    clause( result, nc,   a,  b);
                    clause( result,  c,  na,  b);
                    clause( result,  c,   a, nb);
                }
            }
        }
        result = mkLit(var(result),sign(f));
        vmapp.set(f,result);
    }

    assert(result != lit_Undef);

    return result;
}

Lit Clausifier::basicClausify(Formula f)
{
    Var result = var_Undef;

    if (Atom_p(f)){
        assert(!Const_p(f));
        result = index(f);
    }else if (vmap.at(f) != var_Undef && !s.isEliminated(vmap.at(f))){
        result = vmap.at(f);
    }else{
#ifdef MINISAT
        result = s.newVar(l_Undef, !opt_branch_pbvars);
#else
        result = s.newVar(true /*l_Undef*/, !opt_branch_pbvars);
#endif
        Lit p  = mkLit(result);
        if (Bin_p(f)){

            if (op(f) == op_And){
                vec<Formula> conj;
                collect(f, conj);
                assert(conj.size() > 1);
                for (int i = 0; i < conj.size(); i++)
                    clause(~p,basicClausify(conj[i]));

                tmp_clause.clear();
                tmp_clause.push(p);
                for (int i = 0; i < conj.size(); i++)
                    tmp_clause.push(~basicClausify(conj[i]));
                s.addClause(tmp_clause);
            }else{

                Lit l = basicClausify(left (f));
                Lit r = basicClausify(right(f));

                //printf("equiv:\n");
                assert(op(f) == op_Equiv);
                clause(~p, ~l,  r);
                clause(~p,  l, ~r);
                clause( p, ~l, ~r);
                clause( p,  l,  r);
            }
        }else if (ITE_p(f)){
            Lit c = basicClausify(cond(f));
            Lit a = basicClausify(tt  (f));
            Lit b = basicClausify(ff  (f));
	    clause(~p, ~c,  a);
	    clause(~p,  c,  b);
	    clause( p, ~c, ~a);
	    clause( p,  c, ~b);

	    // not neccessary !!
	    clause(~a, ~b,  p);
	    clause( a,  b, ~p);
        }else{
            assert(FA_p(f));

            Lit a = basicClausify(FA_x(f));
            Lit b = basicClausify(FA_y(f));
            Lit c = basicClausify(FA_c(f));

            if (isCarry(f)){
                //printf("carry:\n");
                clause(~p,  a,  b);
                clause(~p,  c,  a);
                clause(~p,  c,  b);
                clause( p, ~c, ~a);
                clause( p, ~c, ~b);
                clause( p, ~a, ~b);
            }else{
                //printf("sum:\n");
                clause(~p, ~c,  ~a,  b);
                clause(~p, ~c,   a, ~b);
                clause(~p,  c,  ~a, ~b);
                clause(~p,  c,   a,  b);
                clause( p, ~c,  ~a, ~b);
                clause( p, ~c,   a,  b);
                clause( p,  c,  ~a,  b);
                clause( p,  c,   a, ~b);
            }
        }
        vmap.set(f,result);
    }

    assert(result != var_Undef);

    return mkLit(result,sign(f));
}


void clausify(SimpSolver& s, const vec<Formula>& fs, vec<Lit>& out)
{
    Clausifier c(s);

    for (int i = 0; i < fs.size(); i++)
        c.usage(fs[i]);

    if (opt_convert_weak) 
        for (int i = 0; i < fs.size(); i++)
            out.push(c.polarityClausify(fs[i]));
    else
        for (int i = fs.size()-1; i >= 0; i--) {
            out.push(c.basicClausify(fs[i]));
	    if (!opt_shared_fmls && !opt_reuse_sorters) {
	        int diff = FEnv::nodes.size() - FEnv::stack.last();
	        if (diff > 1000) FEnv::nodes.shrink(diff);
		FEnv::stack.pop();
	    }
	}
    if (!opt_shared_fmls && !opt_reuse_sorters) {
        FEnv::clear(); FEnv::stack.clear();
        clear_clausifier_static_maps();
    }
}


void clausify(SimpSolver& s, const vec<Formula>& fs)
{
    vec<Lit>  out;
    clausify(s, fs, out);
    extern MsSolver *pb_solver;
    if (pb_solver->use_base_assump && out.size() == 1)
        pb_solver->base_assump.push(out[0]);
    else
        for (int i = 0; i < out.size(); i++)
            if (pb_solver->ipamir_used)
                pb_solver->addUnitClause(out[i]);
            else
                s.addClause(out[i]);
}
