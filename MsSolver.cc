/**************************************************************************************[MsSolver.cc]
  Copyright (c) 2018-2021, Marek Piotrów

  Based on PbSolver.cc ( Copyright (c) 2005-2010, Niklas Een, Niklas Sorensson)

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

#include <unistd.h>
#include <signal.h>
#include "System.h"
#include "Sort.h"
#include "Debug.h"
#include <cstdlib>
#include <queue>
#include <vector>
#include <set>
#ifdef USE_SCIP
#include <atomic>
    extern std::atomic<bool> SCIP_found_opt; 
#endif                

template<typename int_type>
static int_type gcd(int_type small, int_type big) {
    if (small < 0) small = -small;
    if (big < 0) big = -big;
    return (small == 0) ? big: gcd(big % small, small); }

template<typename T>
static int bin_search(const Minisat::vec<T>& seq, const T& elem)
{
    int fst = 0, cnt = seq.size();
    while (cnt > 0) {
        int step = cnt / 2, mid = fst + step;
        if (seq[mid] < elem) fst = mid + 1, cnt -= step + 1; 
        else cnt = step;
    }
    return (fst < seq.size() && seq[fst] == elem ? fst : -1);
}
        
template<typename T>
static int bin_search(const vec<T>& seq, const T& elem)
{
    int fst = 0, cnt = seq.size();
    while (cnt > 0) {
        int step = cnt / 2, mid = fst + step;
        if (seq[mid] < elem) fst = mid + 1, cnt -= step + 1; 
        else cnt = step;
    }
    return (fst < seq.size() && seq[fst] == elem ? fst : -1);
}
        
static MsSolver *pb_solver;
static
void SIGINT_interrupt(int signum) { 
    pb_solver->sat_solver.interrupt(); pb_solver->asynch_interrupt=true; 
#ifdef SIGXCPU    
    pb_solver->cpu_interrupt = (signum == SIGXCPU);
#else
    (void) signum;
    pb_solver->cpu_interrupt = false;
#endif
}

extern int verbosity;

static void clear_assumptions(Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs)
{
    int removed, j = 0;
    for (int i = 0; i < assump_ps.size(); i++) {
        if (assump_Cs[i] < 0) continue;
        if (j < i) assump_ps[j] = assump_ps[i], assump_Cs[j] = assump_Cs[i];
        j++;
    }
    if ((removed = assump_ps.size() - j) > 0)
        assump_ps.shrink(removed), assump_Cs.shrink(removed);
}

static
bool satisfied_soft_cls(Minisat::vec<Lit> *cls, vec<bool>& model)
{
    assert(cls != NULL);
    for (int i = cls->size() - 2; i >= 0; i--)
        if ((( sign((*cls)[i]) && !model[var((*cls)[i])]) 
          || (!sign((*cls)[i]) &&  model[var((*cls)[i])])))
            return true;
    return false;
}

Int evalGoal(const vec<Pair<weight_t, Minisat::vec<Lit>* > >& soft_cls, 
        vec<bool>& model, Minisat::vec<Lit>&soft_unsat)
{
    Int sum = 0;
    bool sat = false;
    soft_unsat.clear();
    for (int i = 0; i < soft_cls.size(); i++) {
        Lit p = soft_cls[i].snd->last(); if (soft_cls[i].snd->size() == 1) p = ~p;
        if ((( sign(p) && !model[var(p)]) || (!sign(p) &&  model[var(p)])) 
            && !(sat = satisfied_soft_cls(soft_cls[i].snd, model))) {
            if (opt_output_top > 0) soft_unsat.push(~p);
            sum += soft_cls[i].fst;
        } else if (opt_output_top > 0) {
            soft_unsat.push(p);
        }
        if (sat) { sat = false; model[var(p)] = !model[var(p)]; }
    }
    return sum;
}

static
void core_minimization(SimpSolver &sat_solver, Minisat::vec<Lit> &mus)
{
    int last_size = sat_solver.conflict.size();

    sat_solver.setConfBudget(1000);
    int verb = sat_solver.verbosity; sat_solver.verbosity = 0;
    for (int i = 0; last_size > 1 && i < last_size; ) {
        Lit p = mus[i];
        for (int j = i+1; j < last_size; j++) mus[j-1] = mus[j];
        mus.pop();
        if (sat_solver.solveLimited(mus) != l_False) {
            mus.push();
            for (int j = last_size - 1; j > i; j--) mus[j] = mus[j-1];
            mus[i] = p; i++;
        } else last_size--;
    }
    sat_solver.budgetOff(); sat_solver.verbosity = verb;

    for (int i = mus.size() - 1; i >= 0; i--) mus[i] = ~mus[i];
}

/*static void core_trimming(SimpSolver &sat_solver, int max_size, int n)
{
    int last_size = sat_solver.conflict.size();
    Minisat::vec<Lit> assump(last_size);
    for (int i = n; i > 0 && last_size > max_size; i--) {
        assump.clear();
        for (int j = 0; j < last_size; j++) assump.push(~sat_solver.conflict[j]);
        sat_solver.solve(assump);
        if (sat_solver.conflict.size() >= last_size) return;
        last_size = sat_solver.conflict.size();
    }
}*/

static Int next_sum(Int bound, const vec<Int>& cs)
{ // find the smallest sum of a subset of cs that is greater that bound
    vec<Int> sum[2];
    Int x, next_min = Int_MAX;
    int oldv =0, newv = 1, lst = 0;

    sum[oldv].push(0); ++bound;
    for (int sz = 1, j = 0; j < cs.size(); j++, oldv = newv, newv = 1-oldv, lst = 0) {
        for (int i = 0; i < sz; i++)
            if ((x = sum[oldv][i] + cs[j]) < bound) {
                while (lst < sz && sum[oldv][lst] > x) sum[newv].push(sum[oldv][lst++]);
                if (lst == sz || sum[oldv][lst] < x) sum[newv].push(x);
            } else if (x < next_min) {
                if (x == bound) return x;
                next_min = x;
            }
        while (lst < sz) sum[newv].push(sum[oldv][lst++]);
        sz = sum[newv].size(); sum[oldv].clear();
    }
    return (next_min == Int_MAX ? bound - 1 : next_min);

}

/*static
Int evalPsCs(vec<Lit>& ps, vec<Int>&Cs, vec<bool>& model)
{
    Int sum = 0;
    assert(ps.size() == Cs.size());
    for (int i = 0; i < ps.size(); i++){
        if (( var(ps[i]) >= model.size())
        ||  ( sign(ps[i]) && model[var(ps[i])] == false)
        ||  (!sign(ps[i]) && model[var(ps[i])] == true )
        )
            sum += Cs[i];
    }
    return sum;
}

static
Int evalPsCs(vec<Lit>& ps, vec<Int>&Cs, Minisat::vec<lbool>& model)
{
    Int sum = 0;
    assert(ps.size() == Cs.size());
    for (int i = 0; i < ps.size(); i++){
        if (( sign(ps[i]) && model[var(ps[i])] == l_False)
        ||  (!sign(ps[i]) && model[var(ps[i])] == l_True )
        )
            sum += Cs[i];
    }
    return sum;
}

static void opt_stratification(vec<weight_t>& sorted_assump_Cs, vec<Pair<Int, bool> >& sum_sorted_soft_cls)
{
    assert(sorted_assump_Cs.size() == sum_sorted_soft_cls.size());

    int m = max(1, sum_sorted_soft_cls.size() - 10);
    if (m < 10) m = 1;
    for (int i = sum_sorted_soft_cls.size() - 1; i >= m; i--)
        if (sorted_assump_Cs[i] > sorted_assump_Cs[i-1] + 1 || 
                i < sum_sorted_soft_cls.size() - 1 && !sum_sorted_soft_cls[i + 1].snd) 
            sum_sorted_soft_cls[i].snd = true;
    if (m == 1) return;
    vec<Pair<weight_t, int> > gaps;
    for (int i = 0; i < m; i++) gaps.push(Pair_new(sorted_assump_Cs[i+1] - sorted_assump_Cs[i], i + 1));
    Sort::sort(gaps);
    for (int i = gaps.size() - 1, j = 0; j < 10; j++, i--) sum_sorted_soft_cls[gaps[i].snd].snd = true;
}*/

template <class T> struct LT {bool operator()(T x, T y) { return x.snd->last() < y.snd->last(); }};
template <class T> struct wLT {bool operator()(T x, T y) { return x.fst < y.fst; }};
template <class T> struct lLT {bool operator()(T x, T y) { return x < y; }};

static weight_t do_stratification(SimpSolver& S, vec<weight_t>& sorted_assump_Cs, vec<Pair<weight_t,
        Minisat::vec<Lit>* > >& soft_cls, int& top_for_strat, Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs)
{
    weight_t  max_assump_Cs;
    max_assump_Cs = sorted_assump_Cs.last(); sorted_assump_Cs.pop();
    if (sorted_assump_Cs.size() > 0 && sorted_assump_Cs.last() == max_assump_Cs - 1) 
        max_assump_Cs = sorted_assump_Cs.last(), sorted_assump_Cs.pop(); 
    int start = top_for_strat - 1;
    while (start >= 0 && soft_cls[start].fst >= max_assump_Cs) start--;
    start++;
    if (start < top_for_strat) {
        int sz = top_for_strat - start, to = 0, fr = sz;
        Sort::sort(&soft_cls[start], sz, LT<Pair<weight_t, Minisat::vec<Lit>*> >());
        assump_ps.growTo(assump_ps.size() + sz); assump_Cs.growTo(assump_Cs.size() + sz);
        for (int i = assump_ps.size() - 1; i >= sz; i--)
            assump_ps[i] = assump_ps[i-sz], assump_Cs[i] = assump_Cs[i-sz];
        for (int i = start; i < top_for_strat; i++) {
            Lit p = ~soft_cls[i].snd->last();
            if (soft_cls[i].snd->size() > 1) S.addClause(*soft_cls[i].snd); else p = ~p;
            while (fr < assump_ps.size() && assump_ps[fr] <= p)
                assump_ps[to] = assump_ps[fr], assump_Cs[to++] = assump_Cs[fr++];
            assump_ps[to] = p; assump_Cs[to++] = soft_cls[i].fst;
        }
        Sort::sort(&soft_cls[start], sz);
        top_for_strat = start;
    }
    return max_assump_Cs;
}

void MsSolver::harden_soft_cls(Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs, vec<weight_t>& sorted_assump_Cs, IntLitQueue& delayed_assump, Int& delayed_assump_sum)
{
    int cnt_unit = 0, cnt_assump = 0, sz = 0;
    Int Ibound = UB_goalvalue - LB_goalvalue, WMAX = Int(WEIGHT_MAX);
    weight_t       wbound = (Ibound >= WMAX ? WEIGHT_MAX : tolong(Ibound));
    weight_t ub_goalvalue = (UB_goalvalue >= WMAX ? WEIGHT_MAX : tolong(UB_goalvalue - fixed_goalval));
    for (int i = top_for_hard - 1; i >= 0 && soft_cls[i].fst > wbound; i--) { // hardening soft clauses with weights > the current goal interval length 
        if (soft_cls[i].fst > ub_goalvalue) sz++;
        Lit p = soft_cls[i].snd->last(); if (soft_cls[i].snd->size() > 1) p = ~p;
        int j = bin_search(assump_ps, p);
        if (j >= 0 && assump_Cs[j] > Ibound) {
            if (opt_minimization == 1) harden_lits.set(p, Int(soft_cls[i].fst));
            assump_Cs[j] = -assump_Cs[j]; // mark a corresponding assumption to be deleted
            cnt_assump++; cnt_unit++; sat_solver.addClause(p);
        } else if (soft_cls[i].fst > ub_goalvalue) { 
            if (opt_minimization == 1) {
                harden_lits.set(p, Int(soft_cls[i].fst));
                if (i <= top_for_strat && soft_cls[i].snd->size() > 1) 
                    sat_solver.addClause(*soft_cls[i].snd);
            }
            cnt_unit++, sat_solver.addClause(p);
        }
    }
    if (opt_verbosity >= 2 && cnt_unit > 0) reportf("Hardened %d soft clauses\n", cnt_unit);
    if (sz > 0 ) {
        top_for_hard -= sz;
        if (top_for_strat > top_for_hard) top_for_strat = top_for_hard;
        weight_t hard_weight = soft_cls[top_for_hard].fst;
        while (sorted_assump_Cs.size() > 0 && sorted_assump_Cs.last() >= hard_weight) sorted_assump_Cs.pop();
        while (!delayed_assump.empty() && delayed_assump.top().fst >= hard_weight)
            delayed_assump_sum -= delayed_assump.top().fst, delayed_assump.pop();
    }
    if (cnt_assump > 0) clear_assumptions(assump_ps, assump_Cs);
}

void MsSolver::optimize_last_constraint(vec<Linear*>& constrs, Minisat::vec<Lit>& assump_ps, Minisat::vec<Lit>& new_assump)
{
    Minisat::vec<Lit> assump;
    if (constrs.size() == 0) return ;
    int verb = sat_solver.verbosity; sat_solver.verbosity = 0;
    bool found = false;

    sat_solver.setConfBudget(1000);
    if (sat_solver.solveLimited(assump_ps) == l_False) {
        for (int i=0; i < sat_solver.conflict.size(); i++)
            if (assump_ps.last() == ~sat_solver.conflict[i]) { found = true; break;}
        if (found) {
            if (constrs.size() > 1) {
                constrs[0] = constrs.last();
                constrs.shrink(constrs.size() - 1);
            }
            while (found && (constrs[0]->lo > 1 || constrs[0]->hi < constrs[0]->size - 1)) {
                if (constrs[0]->lo > 1) --constrs[0]->lo; else ++constrs[0]->hi;
                constrs[0]->lit = lit_Undef;
                convertPbs(false);
                Lit newp = constrs[0]->lit;
                sat_solver.setFrozen(var(newp),true);
                sat_solver.addClause(~assump_ps.last(), newp);
                new_assump.push(assump_ps.last()); assump_ps.last() = newp;
                if (sat_solver.solveLimited(assump_ps) != l_False) break;
                found = false;
                for (int i=0; i < sat_solver.conflict.size(); i++)
                    if (assump_ps.last() == ~sat_solver.conflict[i]) { found = true; break;}
            }
        }
    }
    sat_solver.budgetOff(); sat_solver.verbosity = verb;
}

static inline int log2(int n) { int i=0; while (n>>=1) i++; return i; }

///////////////////////////////////////////////////////////////////////////
// For every literal have an ordered vector of clauses where it appears.
void MsSolver::set_lits_in_clauses(){
    if (hards != -1) return;
    Sort::sort(&all_cls[0], all_cls.size(), wLT<Pair<weight_t, Minisat::vec<Lit>*> >());

    int A = all_cls.size();
    int H = A;
    for(int i = 0; i < A; i ++){
        if(all_cls[i].fst != -1){
            H = i;
            break;
        }
    }
    hards = H;

    lits_in_clauses.growTo(declared_n_vars * 2);
    for(int i = 0; i < declared_n_vars * 2; i ++)
        lits_in_clauses[i] = new vec<int>();

    for(int i = 0; i < A; i ++){
        bool is_soft = (i >= H);
        int max_v = max(1, all_cls[i].snd->size() - is_soft);  

        for(int j = 0; j < max_v; j ++){
            int i_lit = toInt((*all_cls[i].snd)[j]);
            lits_in_clauses[i_lit]->push(i);
        }
    }    
}
bool MsSolver::first_sat_based_model(vec<bool>& model, int& H){    
    for (Var x = 0; x < model.size(); x ++)
        sat_solver.setFrozen(x, true);

    lbool status = sat_solver.solveLimited(Minisat::vec<Lit>());
    if (status != l_True) return 0;

    for (Var x = 0; x < declared_n_vars; x++)
        model[x] = (sat_solver.modelValue(x) == l_True);
    return 1;
}
bool polarity(Lit p){
    return !sign(p);
}
void MsSolver::value_hard_clause(vec<int>& unvalued_lits, vec<bool>& model, vec<bool>& set_vars, int& c){
    unvalued_lits[c] = 0;
    int H = unvalued_lits.size();

    for(int j = 0; j < all_cls[c].snd->size(); j ++){
        Lit p = (*all_cls[c].snd)[j];
        
        if(set_vars[var(p)]) continue;

        set_vars[var(p)] = true;
        model[var(p)] = !sign(p); 
            
        for(int i = 0; i < lits_in_clauses[toInt(p)]->size(); i ++){
            int k = (*lits_in_clauses[toInt(p)])[i];
            if (k >= H) break;
            unvalued_lits[k] = 0;
        }
        for(int i = 0; i < lits_in_clauses[toInt(~p)]->size(); i ++){
            int k = (*lits_in_clauses[toInt(~p)])[i];
            if (k >= H) break;
            if(unvalued_lits[k] > 0) unvalued_lits[k] = unvalued_lits[k] - 1;
            if(unvalued_lits[k] == 1) value_hard_clause(unvalued_lits, model, set_vars, k);
        }
        return;
    }
    reportf("Error! Hard clause unsatisfied! All literals are already valued.\n");
    return;
}
// Run unit propagation on hard clauses and then set random values.
void MsSolver::run_up(vec<bool>& model, const int& H){
    vec<int> unvalued_lits;
    unvalued_lits.growTo(H);

    int V = model.size();
    vec<bool> set_vars;
    set_vars.growTo(V, 0);

    for(int c = 0; c < H; c ++) 
        unvalued_lits[c] = all_cls[c].snd->size();
    
    for(int c = 0; c < H; c ++) 
        if(unvalued_lits[c] == 1)
            value_hard_clause(unvalued_lits, model, set_vars, c);

    for(int x = 0; x < V; x ++){
        if(!set_vars[x]) model[x] = rand() % 2;
    }
}
// Run distUp algorithm for the given <num> second.
// From Tailoring Local Search for Partial MaxSAT, 2014
bool MsSolver::run_dist(const int& time_limit){
    int A = all_cls.size(), V = declared_n_vars;
    int pp = 10;
    if(V > 2500) pp = 1;    

    if(hards == -1) set_lits_in_clauses();
    int H = hards;

    Metrics m(V, A, H);
    m.initialize_metrics(0);

    if (!opt_only_hards or !first_sat_based_model(m.model, H)){
        run_up(m.model, H);
    }
    for(int i = 0; i < A; i ++){
        int w = all_cls[i].fst;
        int sat = 0;
        bool s = (i >= H);
        int maxi = max(1, all_cls[i].snd->size() - s);           
        for(int j = 0; j < maxi; j ++){
            Lit p = (*all_cls[i].snd)[j];
            if (m.model[var(p)] == polarity(p)) {
                sat ++;
                m.last_sat[i] = var(p);
            }
        }
        m.sat_cnt[i] = sat;
        if (!sat) {        
            m.add_unsat(i, w);
            for(int j = 0; j < maxi; j ++){
                Var q = var((*all_cls[i].snd)[j]);   
                m.update_score(s, q, abs(w));
            }
        } else if (sat == 1) m.update_score(s, m.last_sat[i], -abs(w));
    }
    for(Var x = 0; x < V; x ++){
        if(m.hscore[x] > 0) 
            increasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, x);
        else if(m.hscore[x] == 0 and m.sscore[x] > 0)
            increasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, x);
    }

    bool found_solution = false;
    extern time_t wall_clock_time;

    while(difftime(time(NULL), wall_clock_time) < time_limit){
        if(m.is_the_best()) {
            best_goalvalue = m.model_scost;
            char* tmp = toString(m.model_scost);    
            printf("o %s\n", tmp), fflush(stdout);            

            m.model.copyTo(best_model);
            found_solution = true;
        }

        Var x = -1;
        if(m.cnt_hplus_scores > 0){
            int r = rand() % m.cnt_hplus_scores;
            x = m.hplus_scores[r];
        } else if (m.cnt_hzero_scores > 0){
            x = m.hzero_scores[0];
            for(int i = 1; i < m.cnt_hzero_scores; i ++)
                if(m.sscore[m.hzero_scores[i]] > m.sscore[x]) x = m.hzero_scores[i];
        } 
        if(x == -1){
            // update weights
            if (rand() % 10000 < pp) {
                for(int i = 0; i < m.cnt_sat_hard_bigs; i ++){
                    int cl = m.sat_hard_bigs[i];
                    all_cls[cl].fst ++;         

                    if(m.sat_cnt[cl] == 1){
                        Var q = m.last_sat[cl];  

                        if(m.hscore[q] == 0 and m.sscore[q] > 0) 
                            decreasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                        if(m.hscore[q] <= 0 and m.hscore[q] + 1 > 0)
                            increasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, q);
                        else if(m.hscore[q] + 1 == 0 and m.sscore[q] > 0)
                            increasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                        m.hscore[q] += 1;
                    }
                    if(all_cls[cl].fst == -1)
                        decreasePointerList(m.sat_hard_bigs, m.sat_hard_bigs_idx, m.cnt_sat_hard_bigs, cl);                    
                }
            } else {
                for(int i = 0; i < m.cnt_unsat_hards; i ++){
                    int cl = m.unsat_hards[i];
                    // weights of unsat hards are increased -> hscore of q should be increased as well
                    all_cls[cl].fst --;       
                    m.model_hcost += 1;

                    for(int j = 0; j < all_cls[cl].snd->size(); j ++){
                        Var q = var((*all_cls[cl].snd)[j]);
                        if(m.hscore[q] == 0 and m.sscore[q] > 0) 
                            decreasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                        if(m.hscore[q] <= 0 and m.hscore[q] + 1 > 0)
                            increasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, q);
                        else if(m.hscore[q] + 1 == 0 and m.sscore[q] > 0)
                            increasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                        m.hscore[q] += 1;
                    }
                }                                
            }
            // choose variable to flip 
            // with the priority on positive hard cost then soft cost then random
            int idx = -1;
            if (m.model_hcost > 0) {
                int r = rand() % m.cnt_unsat_hards;
                idx = m.unsat_hards[r];
            } else if (m.model_scost > 0){
                int r = rand() % m.cnt_unsat_softs;
                idx = m.unsat_softs[r];                
            }
            x = var((*all_cls[idx].snd)[0]);
            bool s = (idx >= H);
            int maxi = max(1, all_cls[idx].snd->size() - s);

            for(int j = 1; j < maxi; j ++){
                Lit p = (*all_cls[idx].snd)[j];
                if (m.sscore[var(p)] > m.sscore[x]) x = var(p);
            }
        }
        Lit xp = mkLit(x, 1 - m.model[x]);       

        for(int i = 0; i < lits_in_clauses[toInt(xp)]->size(); i ++){
            int cl = (*lits_in_clauses[toInt(xp)])[i];
            int w = all_cls[cl].fst;
            bool s = (cl >= H);
            int maxi = max(1, all_cls[cl].snd->size() - s);
            if(m.sat_cnt[cl] == 2){                
                for(int j = 0; j < maxi; j ++){
                    Lit p = (*all_cls[cl].snd)[j];
                    Var q = var(p);
                    if (p != xp and m.model[q] != sign(p)) {
                        m.last_sat[cl] = q;
                        break;
                    }
                }
                Var q = m.last_sat[cl];
                if(!s){
                    int hw = -w;
                    if(m.hscore[q] == 0 and m.sscore[q] > 0)
                        decreasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                    if(m.hscore[q] > 0 and m.hscore[q] - hw <= 0)
                        decreasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, q);
                    if(m.hscore[q] - hw == 0 and m.sscore[q] > 0)
                        increasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                    m.hscore[q] -= hw;
                } else {
                    if(m.hscore[q] == 0 and m.sscore[q] > 0 and m.sscore[q] - w <= 0)
                        decreasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                    m.sscore[q] -= w;
                }
            }
            else if(m.sat_cnt[cl] == 1){
                m.add_unsat(cl, w);
                if(all_cls[cl].fst < -1)
                    decreasePointerList(m.sat_hard_bigs, m.sat_hard_bigs_idx, m.cnt_sat_hard_bigs, cl);
                for(int j = 0; j < maxi; j ++){
                    Var q = var((*all_cls[cl].snd)[j]);
                    if(!s){
                        int hw = -w;
                        if(m.hscore[q] == 0 and m.sscore[q] > 0)
                            decreasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                        if(m.hscore[q] <= 0 and m.hscore[q] + hw > 0)
                            increasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, q);
                        if(m.hscore[q] + hw == 0 and m.sscore[q] > 0)
                            increasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                        m.hscore[q] += hw;
                    } else {
                        if(m.hscore[q] == 0 and m.sscore[q] <= 0 and m.sscore[q] + w > 0)
                            increasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                        m.sscore[q] += w;    
                    }
                }
                if(!s){
                    int hw = -w;
                    if(m.hscore[x] == 0 and m.sscore[x] > 0)
                        decreasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, x);
                    if(m.hscore[x] <= 0 and m.hscore[x] + hw > 0)
                        increasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, x);
                    if(m.hscore[x] + hw == 0 and m.sscore[x] > 0)
                        increasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, x);
                    m.hscore[x] += hw;
                } else {
                    if(m.hscore[x] == 0 and m.sscore[x] <= 0 and m.sscore[x] + w > 0)
                        increasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, x);
                    m.sscore[x] += w;
                }
            }             
            m.sat_cnt[cl] --;
        }                
        xp = ~xp;
        for(int i = 0; i < lits_in_clauses[toInt(xp)]->size(); i ++){
            int cl = (*lits_in_clauses[toInt(xp)])[i];            
            int w = all_cls[cl].fst;
            bool s = (cl >= H);
            int maxi = max(1, all_cls[cl].snd->size() - s);
            if(m.sat_cnt[cl] == 1){
                Var q = m.last_sat[cl];
                if(!s){
                    int hw = -w;
                    if(m.hscore[q] == 0 and m.sscore[q] > 0)
                        decreasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                    if(m.hscore[q] <= 0 and m.hscore[q] + hw > 0)
                        increasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, q);
                    if(m.hscore[q] + hw == 0 and m.sscore[q] > 0)
                        increasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                    m.hscore[q] += hw;
                }   else {
                        if(m.hscore[q] == 0 and m.sscore[q] <= 0 and m.sscore[q] + w > 0)
                            increasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                        m.sscore[q] += w;    
                }
            } else if(m.sat_cnt[cl] == 0){
                m.subtract_unsat(cl, w);

                if(all_cls[cl].fst < -1)
                    increasePointerList(m.sat_hard_bigs, m.sat_hard_bigs_idx, m.cnt_sat_hard_bigs, cl);                    
                m.last_sat[cl] = x;
                for(int j = 0; j < maxi; j ++){
                    Var q = var((*all_cls[cl].snd)[j]);
                    if(!s){
                        int hw = -w;
                        if(m.hscore[q] == 0 and m.sscore[q] > 0)
                            decreasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                        if(m.hscore[q] > 0 and m.hscore[q] - hw <= 0)
                            decreasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, q);
                        if(m.hscore[q] - hw == 0 and m.sscore[q] > 0)
                            increasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                        m.hscore[q] -= hw;
                    } else {
                        if(m.hscore[q] == 0 and m.sscore[q] > 0 and m.sscore[q] - w <= 0)
                            decreasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, q);
                        m.sscore[q] -= w;
                    }
                }
                if(!s){
                    int hw = -w;
                    if(m.hscore[x] == 0 and m.sscore[x] > 0)
                        decreasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, x);
                    if(m.hscore[x] > 0 and m.hscore[x] - hw <= 0)
                        decreasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, x);
                    if(m.hscore[x] - hw == 0 and m.sscore[x] > 0)
                        increasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, x);
                    m.hscore[x] -= hw;
                } else {
                    if(m.hscore[x] == 0 and m.sscore[x] > 0 and m.sscore[x] - w <= 0)
                        decreasePointerList(m.hzero_scores, m.scores_idx, m.cnt_hzero_scores, x);
                    m.sscore[x] -= w;
                }
            }
            m.sat_cnt[cl] ++;
        }
        m.model[x] = m.model[x] ^ 1;
    }
    return found_solution;
}
void MsSolver::decimation_with_unit_propagation(vec<bool>& model, int& hards){
    int alls = all_cls.size();
    int softs = alls - hards;
    int vars = model.size();

    vec<long long> soft_make;
    soft_make.growTo(vars * 2);
// 
    vec<int> unassigned, assign_idx;
    unassigned.growTo(vars, 0);
    assign_idx.growTo(vars);
    int cnt_unassigned = 0;
    for(int i = 0; i < vars; i ++)
        increasePointerList(unassigned, assign_idx, cnt_unassigned, i);

    vec<int> unit_soft, unit_hard, unit_hard_idx, unit_soft_idx;
    // literały które są w jakiejś unit klauzurze
    unit_soft.growTo(softs);
    unit_hard.growTo(hards);
    unit_hard_idx.growTo(vars);
    unit_soft_idx.growTo(vars);
    int cnt_unit_soft = 0, cnt_unit_hard = 0;

    vec<int> has_unit_soft, has_unit_hard;
    has_unit_soft.growTo(vars, 0);
    has_unit_hard.growTo(vars, 0);

    vec<bool> unvalued;
    vec<bool> value_set;
    unvalued.growTo(alls, 1);
    value_set.growTo(vars, 0);
    
    for(int i = 0; i < alls; i ++){
        bool s = (i >= hards);
        int maxi = max(1, all_cls[i].snd->size() - s);
        if(maxi == 1){
            Lit p = (*all_cls[i].snd)[0];
            int h = 0;
            if(s) {
                h = has_unit_soft[var(p)];
                if(h == 0) increasePointerList(unit_soft, unit_soft_idx, cnt_unit_soft, var(p));                
            } else {
                h = has_unit_hard[var(p)];
                if(h == 0) increasePointerList(unit_hard, unit_hard_idx, cnt_unit_hard, var(p));                
            }            
            // zmienna pozytywna w unit dostaje 10, negatywna dostaje 1
            if(sign(p) and h < 10) h += 10;
            if(!sign(p) and h % 10 != 1) h += 1;            
            if(s) has_unit_soft[var(p)] = h;
            else has_unit_hard[var(p)] = h;
        }
    }    
    for(int i = hards; i < alls; i ++){
        int maxi = max(1, all_cls[i].snd->size() - 1);
        for(int j = 0; j < maxi; j ++){
            Lit p = (*all_cls[i].snd)[j];
            soft_make[toInt(p)] += all_cls[i].fst;
        }
    }
    while(cnt_unassigned > 0){
        int x;
        if(cnt_unit_hard > 0){
            // reportf("unit hard\n");
            int r = rand() % cnt_unit_hard;
            x = unit_hard[r];

            if(value_set[x]){
                decreasePointerList(unit_hard, unit_hard_idx, cnt_unit_hard, x);            
                continue;
            }                        
            if(has_unit_hard[x] == 11) // model[x] = rand() % 2;
            {
                if(soft_make[x*2] <= 0 and soft_make[x*2+1] <= 0) model[x] = rand() % 2;
                else {
                    if (soft_make[x*2] > soft_make[x*2+1]) model[x] = 1;
                    else model[x] = 0;
                }
            }
            else if(has_unit_hard[x] == 10) model[x] = 0;
            else if(has_unit_hard[x] == 1) model[x] = 1;
            else { reportf("error\n"); return; }

            decreasePointerList(unassigned, assign_idx, cnt_unassigned, x);
            decreasePointerList(unit_hard, unit_hard_idx, cnt_unit_hard, x);            
        } else if (cnt_unit_soft > 0){
            // reportf("unit soft\n");
            // int r = rand() % cnt_unit_soft;
            // x = unit_soft[r];
            x = unit_soft[0];
            long long ms = max(soft_make[x*2], soft_make[x*2+1]);
            int t = 15;
            if(cnt_unit_soft > t){
                x = unit_soft[rand() % cnt_unit_soft];
                ms = max(soft_make[x*2], soft_make[x*2+1]);
                for(int j = 1; j < t; j ++){
                    int y = unit_soft[rand() % cnt_unit_soft];
                    if(value_set[y]){
                        decreasePointerList(unit_soft, unit_soft_idx, cnt_unit_soft, y);            
                        continue;
                    }
                    long long nms = max(soft_make[y*2], soft_make[y*2+1]); 
                    if(nms > ms or value_set[x]){
                        x = y;
                        ms = nms;
                    }
                }

            } else {
                for(int j = 1; j < cnt_unit_soft; j ++){
                    int y = unit_soft[j];
                    if(value_set[y]){
                        decreasePointerList(unit_soft, unit_soft_idx, cnt_unit_soft, y);            
                        continue;
                    }
                    long long nms = max(soft_make[y*2], soft_make[y*2+1]); 
                    if(nms > ms or value_set[x]){
                        x = y;
                        ms = nms;
                    }
                }
            }

            if(value_set[x]){
                decreasePointerList(unit_soft, unit_soft_idx, cnt_unit_soft, x);            
                continue;
            }
            if(soft_make[x*2] <= 0 and soft_make[x*2+1] <= 0) model[x] = rand() % 2;
            else {
                if (soft_make[x*2] > soft_make[x*2+1]) model[x] = 1;
                else model[x] = 0;
            }

            decreasePointerList(unassigned, assign_idx, cnt_unassigned, x);
            decreasePointerList(unit_soft, unit_soft_idx, cnt_unit_soft, x);            

        } else {
            // reportf("random\n");
            int r = rand() % cnt_unassigned;
            x = unassigned[r];
            model[x] = rand() % 2;
            decreasePointerList(unassigned, assign_idx, cnt_unassigned, x);
        }
        // reportf("x %d\n", x);
        Lit xp = mkLit(x, 1 - model[x]);   
        value_set[x] = 1; 

        for(int i = 0; i < lits_in_clauses[toInt(xp)]->size(); i ++){
            int k = (*lits_in_clauses[toInt(xp)])[i];        
            if(unvalued[k] and k >= hards){
                int s = 1;
                int maxi = max(1, all_cls[k].snd -> size() - s);
                for(int j = 0; j < maxi; j ++){
                    Lit p = ((*all_cls[k].snd)[j]);
                    soft_make[toInt(p)] -= all_cls[k].fst;
                }
            }
            unvalued[k] = 0;
        }
        // reportf("unvalued to 0\n");
        for(int i = 0; i < lits_in_clauses[toInt(~xp)]->size(); i ++){
            int k = (*lits_in_clauses[toInt(~xp)])[i];
            // soft_make[toInt(~xp)] -= all_cls[k].fst;
            if(!unvalued[k]) continue;
            int unv = 0;
            int s = (k >= hards);
            int maxi = max(1, all_cls[k].snd -> size() - s);
            Lit p;
            for(int j = 0; j < maxi; j ++){
                Lit q = ((*all_cls[k].snd)[j]);
                if(value_set[var(q)] == 0) {
                    unv ++;
                    p = q;
                }
                if(unv > 1) break;
            }
            if(unv == 1){
                int h = 0;
                if(s) {
                    h = has_unit_soft[var(p)];
                    if(h == 0) increasePointerList(unit_soft, unit_soft_idx, cnt_unit_soft, var(p));
                } else {
                    h = has_unit_hard[var(p)];
                    if(h == 0) increasePointerList(unit_hard, unit_hard_idx, cnt_unit_hard, var(p));
                }            
                if(sign(p) and h < 10) h += 10;
                if(!sign(p) and h % 10 != 1) h += 1;            

                if(s) has_unit_soft[var(p)] = h;
                else has_unit_hard[var(p)] = h;

                unvalued[k] = 0;
            } else if(unv == 0) unvalued[k] = 0;
        }
    }
}
bool MsSolver::run_satlike(bool only_hards, const int& time_limit){
    if(hards == -1) set_lits_in_clauses();
    int H = hards, A = all_cls.size();
    int V = declared_n_vars;
    long double avg_soft_weight = 0;

    vec<weight_t> working_weights;
    working_weights.growTo(A);

    int max_clause_length = 0;
    for(int i = 0; i < A; i ++){
        int s = (i >= H);
        int maxi = max(1, all_cls[i].snd->size() - s);
        max_clause_length = max(max_clause_length, maxi);

        working_weights[i] = all_cls[i].fst;
        if(only_hards and s) working_weights[i] = 0;            
        if(s) avg_soft_weight += all_cls[i].fst;
    }
    avg_soft_weight /= max(1, A-H);

    // SATLike parameters: t-BMS sp-smoothing probability in weighting scheme
    int t = 15, sp = 100000;
    int h_inc = 3, soft_max = 0;
    int max_flips = 10000000, max_non_improve_flips = 10000000;
    if(avg_soft_weight >= 10000){
        h_inc = 300;
        soft_max = 500;
    }
    if (declared_n_vars> 2000) sp = 1;

    // SATLike parameters: random elements instead of the prioritized ones  
    int rdprob = 1, rwprob = 10;

    Metrics m(V, A, H);
    m.initialize_metrics(1);
    
    vec<int> score;
    score.growTo(V,0);
    
    // different options for the initial assignments

    // if(best_goalvalue != INT_MAX and best_model.size() > 0){
        // for(int i = 0; i < model.size(); i ++) model[i] = best_model[i];
    // } else 
    decimation_with_unit_propagation(m.model, V);

    // if(!first_sat_based_model(m.model, H)) return 0;
    
    // for(int i = 0; i < model.size(); i ++){
        // model[i] = rand() % 2;
    // }

    for(int i = 0; i < A; i ++){
        int w = abs(working_weights[i]);
        int sat = 0;
        bool s = (i >= hards);
        int maxi = max(1, all_cls[i].snd->size() - s);           
        for(int j = 0; j < maxi; j ++){
            Lit p = (*all_cls[i].snd)[j];
            if (m.model[var(p)] == polarity(p)) {
                sat ++;
                m.last_sat[i] = var(p);
            }
        }
        m.sat_cnt[i] = sat;
        if (!sat) {        
            if(s) increasePointerList(m.unsat_softs, m.unsat_idx, m.cnt_unsat_softs, i);            
            else increasePointerList(m.unsat_hards, m.unsat_idx, m.cnt_unsat_hards, i);            

            if(s) m.model_scost += all_cls[i].fst;
            else m.model_hcost += 1;
            for(int j = 0; j < maxi; j ++){
                Lit p = (*all_cls[i].snd)[j];
                m.sscore[var(p)] += w;               
            }
        } else {
            increasePointerList(m.sat_clauses, m.unsat_idx, m.cnt_sat_clauses, i);            
            if (sat == 1){
                Var q = m.last_sat[i];
                m.sscore[q] -= w;
            }
        }
    }
    for(Var x = 0; x < V; x ++){
        if(m.sscore[x] > 0) 
            increasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, x);
    }

    bool solution_found = false;
    extern time_t wall_clock_time;

    int sm = 0, inc = 0;
    int step = 1000;
    for(int jj = 0; jj < max_flips; jj ++) {
        if(!time_limit or difftime(time(NULL), wall_clock_time) >= time_limit) break;
        if(m.model_hcost == 0 and m.model_scost < m.best_found){
            max_flips = jj + max_non_improve_flips;
            m.best_found = m.model_scost;
        }
        if(m.model_hcost == 0 and m.model_scost < best_goalvalue){
            best_goalvalue = m.model_scost;
            char* tmp = toString(m.model_scost);    
            printf("o %s\n", tmp), fflush(stdout);            

            m.model.copyTo(best_model);
            solution_found = true;
            if(only_hards) return true;
        }

        Var x = -1;
        if(m.cnt_hplus_scores > 0){     
            int r = rand() % m.cnt_hplus_scores;
            x = m.hplus_scores[r];
            if(rand() % 100 < rdprob);
            else if(m.cnt_hplus_scores < t) {
                for(int j = 0; j < m.cnt_hplus_scores; j ++){                
                    int y = m.hplus_scores[j];
                    if(m.sscore[y] > m.sscore[x] or (m.sscore[y] == m.sscore[x] and m.flip_time[y] < m.flip_time[x])) x = y;
                }
            } else {
                for(int j = 1; j < t; j ++){
                    r = rand() % m.cnt_hplus_scores;
                    int y = m.hplus_scores[r];
                    if(m.sscore[y] > m.sscore[x] or (m.sscore[y] == m.sscore[x] and m.flip_time[y] < m.flip_time[x])) x = y;
                }
            }
        } else {  
            if(rand() % 10000000 < sp){
                sm ++;
                for(int i = 0; i < m.cnt_sat_clauses; i ++){
                    int cl = m.sat_clauses[i];                    
                    long long w1 = working_weights[cl], w2 = working_weights[cl];

                    // zmniejszam wage klauzuli spelnionej
                    if(all_cls[cl].fst == 0) continue;

                    if(w1 < -h_inc) w2 += h_inc;
                    else if(w1 > 1) w2 --;
                    else continue;

                    working_weights[cl] = w2;
                    long long d = abs(w2 - w1);

                    // wiec cofam koszt zmiennej
                    if(m.sat_cnt[cl] == 1){
                        bool s = (cl >= hards);
                        int maxi = max(1, all_cls[cl].snd->size() - s);
                        if(m.last_sat[cl] == -1){
                            for(int j = 0; j < maxi; j ++){
                                Lit p = (*all_cls[cl].snd)[j];
                                Var q = var(p);
                                if (m.model[q] != sign(p)) {
                                    m.last_sat[cl] = q;
                                    break;
                                }
                            }
                        }
                        Var q = m.last_sat[cl]; 
                        if(m.sscore[q] <= 0 and m.sscore[q] + d > 0)
                            increasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, q);
                        m.sscore[q] += d;
                    }
                }   
            } else {
                inc ++; 
                for(int i = 0; i < m.cnt_unsat_hards + m.cnt_unsat_softs; i ++){
                    int cl;
                    if (i < m.cnt_unsat_hards) { cl = m.unsat_hards[i]; }
                    else cl = m.unsat_softs[i - m.cnt_unsat_hards];
                    long long w1 = working_weights[cl], w2 = working_weights[cl];

                    if(all_cls[cl].fst == 0) continue;

                    if(w1 < 0) w2 -= h_inc;
                    else if(w1 <= soft_max) w2 ++;
                    else continue;

                    working_weights[cl] = w2;
                    long long d = abs(w2 - w1);
                
                    bool s = (cl >= hards);
                    int maxi = max(1, all_cls[cl].snd->size() - s);
                    for(int j = 0; j < maxi; j ++){
                        Lit p = (*all_cls[cl].snd)[j];
                        Var q = var(p);
                        if(m.sscore[q] <= 0 and m.sscore[q] + d > 0)
                            increasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, q);
                        m.sscore[q] += d;
                    }                    
                }
            }
            int idx = -1;
            if (m.cnt_unsat_hards > 0) {
                int r = rand() % m.cnt_unsat_hards;                
                idx = m.unsat_hards[r];
            } else if (m.cnt_unsat_softs > 0){
                idx = m.unsat_softs[0];
                m.best_selected[0] = idx;          
                int best_idx_cnt = m.selected_count[idx];                
                int best_selected_cnt = 1;             

                for(int j = 1; j < m.cnt_unsat_softs; j ++){                
                    int idy = m.unsat_softs[j];
                    if(m.selected_count[idy] < best_idx_cnt){
                        best_idx_cnt = m.selected_count[idy];
                        m.best_selected[0] = idy;
                        best_selected_cnt = 1;
                    } else if (m.selected_count[idy] == best_idx_cnt){
                        m.best_selected[best_selected_cnt] = idy;
                        best_selected_cnt ++;
                    }
                }
                idx = m.best_selected[rand() % best_selected_cnt];
                m.selected_count[idx] ++;
            } else { 
                reportf("Error!\n"); 
                return solution_found; 
            }
            x = var((*all_cls[idx].snd)[0]);
            bool s = (idx >= hards);
            int maxi = max(1, all_cls[idx].snd->size() - s);
            if(rand() % 100 < rwprob) x = var((*all_cls[idx].snd)[rand() % maxi]);
            else{
                for(int j = 1; j < maxi; j ++){
                    Lit p = (*all_cls[idx].snd)[j];
                    if (m.sscore[var(p)] > m.sscore[x]) x = var(p);
                }
            }
        }
        Lit xp = mkLit(x, 1 - m.model[x]); 
        int prev_score = m.sscore[x];
        m.flip_time[x] = jj + 1;  
        for(int i = 0; i < lits_in_clauses[toInt(xp)]->size(); i ++){
            int cl = (*lits_in_clauses[toInt(xp)])[i];
            long long w = abs(working_weights[cl]);
            bool s = (cl >= hards);            
            int maxi = max(1, all_cls[cl].snd->size() - s);
            if(m.sat_cnt[cl] == 2){                
                if(m.last_sat[cl] == x or m.last_sat[cl] == -1){
                        for(int j = 0; j < maxi; j ++){
                            Lit p = (*all_cls[cl].snd)[j];
                            Var q = var(p);
                            if (p != xp and m.model[q] != sign(p)) {
                                m.last_sat[cl] = q;
                                break;
                            }
                        }
                }
                if(m.last_sat[cl] == -1) { reportf("seg last sat\n");  continue; return solution_found; }
                Var q = m.last_sat[cl];
                if(m.sscore[q] > 0 and m.sscore[q] - w <= 0)
                    decreasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, q);
                m.sscore[q] -= w;
            }
            else if(m.sat_cnt[cl] == 1){
                decreasePointerList(m.sat_clauses, m.unsat_idx, m.cnt_sat_clauses, cl);

                if(s) increasePointerList(m.unsat_softs, m.unsat_idx, m.cnt_unsat_softs, cl);
                else increasePointerList(m.unsat_hards, m.unsat_idx, m.cnt_unsat_hards, cl);

                for(int j = 0; j < maxi; j ++){
                    Var q = var((*all_cls[cl].snd)[j]);
                    if(m.sscore[q] <= 0 and m.sscore[q] + w > 0)
                        increasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, q);
                    m.sscore[q] += w;
                }
                if(m.sscore[x] <= 0 and m.sscore[x] + w > 0)
                    increasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, x);
                m.sscore[x] += w;

                m.last_sat[cl] = -1;

                if(s) m.model_scost += all_cls[cl].fst;
                else m.model_hcost += 1;
            } else if (m.last_sat[cl] == x) m.last_sat[cl] = -1;
            m.sat_cnt[cl] --;
        }                
        xp = ~xp;
        for(int i = 0; i < lits_in_clauses[toInt(xp)]->size(); i ++){
            int cl = (*lits_in_clauses[toInt(xp)])[i];            
            long long w = abs(working_weights[cl]);
            bool s = (cl >= hards);
            int maxi = max(1, all_cls[cl].snd->size() - s);
            if(m.sat_cnt[cl] == 1){
                if(m.last_sat[cl] == -1){
                    for(int j = 0; j < maxi; j ++){
                        Lit p = (*all_cls[cl].snd)[j];
                        Var q = var(p);
                        if (m.model[q] != sign(p)) {
                            m.last_sat[cl] = q;
                            break;
                        }
                    }
                }
                Var q = m.last_sat[cl];
                if(q == -1) reportf("no last sat\n");
                if(m.sscore[q] <= 0 and m.sscore[q] + w > 0)
                    increasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, q);
                    
                m.sscore[q] += w;
            } else if(m.sat_cnt[cl] == 0){
                if(s) decreasePointerList(m.unsat_softs, m.unsat_idx, m.cnt_unsat_softs, cl);
                else decreasePointerList(m.unsat_hards, m.unsat_idx, m.cnt_unsat_hards, cl);

                increasePointerList(m.sat_clauses, m.unsat_idx, m.cnt_sat_clauses, cl);

                m.last_sat[cl] = x;
                for(int j = 0; j < maxi; j ++){
                    Var q = var((*all_cls[cl].snd)[j]);
                    if(m.sscore[q] > 0 and m.sscore[q] - w <= 0)
                        decreasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, q);
                    m.sscore[q] -= w;
                }
                if(m.sscore[x] > 0 and m.sscore[x] - w <= 0)
                    decreasePointerList(m.hplus_scores, m.scores_idx, m.cnt_hplus_scores, x);
                m.sscore[x] -= w;
                if(s) m.model_scost -= all_cls[cl].fst;
                else m.model_hcost -= 1;
            }
            m.sat_cnt[cl] ++;
        }
        m.model[x] = m.model[x] ^ 1;
    }
    return solution_found;
}
// Run incomplete functions first depending on the given time for them.
// Return true if any solution found then only-hards flag turns to false.
bool MsSolver::start_incomplete()
{
    bool status = false;
    if (opt_dist + opt_satlike > 0){
        set_lits_in_clauses();
    }
    if(opt_dist > 0) {
        if (opt_verbosity > 0) reportf("Run DistUP for %d seconds.\n", opt_dist);
        if(run_dist(opt_dist)) status = true;
    }
    if(opt_satlike > 0) {
        if (opt_verbosity > 0) reportf("Run SATLike 3.0 for %d seconds.\n", opt_satlike);
        if(run_satlike(1, opt_dist + opt_satlike)) {
            status = true;
            run_satlike(0, opt_dist + opt_satlike);
        }
    }
    return status;
}
///////////////////////////////////////////////////////////////////////////
void MsSolver::maxsat_solve(solve_Command cmd)
{
    if(start_incomplete()) opt_only_hards = false;

    if (!okay()) {
        if (opt_verbosity >= 1) sat_solver.printVarsCls();
        return;
    }
#if defined(GLUCOSE3) || defined(GLUCOSE4)    
    if (opt_verbosity >= 1) sat_solver.verbEveryConflicts = 100000;
    sat_solver.setIncrementalMode();
#endif
    if (soft_cls.size() == 0) { opt_maxsat_msu = false; solve(cmd); return; }
    // Convert constraints:
    pb_n_vars = nVars();
    pb_n_constrs = nClauses();
    if (constrs.size() > 0) {
        if (opt_verbosity >= 1)
            reportf("Converting %d PB-constraints to clauses...\n", constrs.size());
        propagate();
        if (!convertPbs(true)){
            if (opt_verbosity >= 1) sat_solver.printVarsCls(constrs.size() > 0);
            assert(!okay()); return;
        }
        if (opt_convert_goal != ct_Undef)
            opt_convert = opt_convert_goal;
    }

    // Freeze goal function variables (for SatELite):
    for (int i = 0; i < soft_cls.size(); i++) {
        sat_solver.setFrozen(var(soft_cls[i].snd->last()), true);
        if (opt_output_top > 0)
            for (int j = soft_cls[i].snd->size() - 2; j >= 0; j--) 
                sat_solver.setFrozen(var((*soft_cls[i].snd)[j]), true);
    }
    sat_solver.verbosity = opt_verbosity - 1;

    if (soft_cls.size() > 0) goal_gcd = soft_cls[0].fst;
    else goal_gcd = 1;

    for (int i = 1; i < soft_cls.size() && goal_gcd != 1; ++i) goal_gcd = gcd(goal_gcd, soft_cls[i].fst);
    if (goal_gcd != 1) {
        if (LB_goalvalue != Int_MIN) LB_goalvalue /= Int(goal_gcd);
        if (UB_goalvalue != Int_MAX) UB_goalvalue /= Int(goal_gcd);
    }
    assert(best_goalvalue == Int_MAX);

    opt_sort_thres *= opt_goal_bias;
    opt_maxsat = opt_shared_fmls = true;

    if (opt_cnf != NULL)
        reportf("Exporting CNF to: \b%s\b\n", opt_cnf),
        sat_solver.toDimacs(opt_cnf),
        exit(0);

    pb_solver = this;
    signal(SIGINT, SIGINT_interrupt);
#ifdef SIGXCPU
    signal(SIGXCPU,SIGINT_interrupt);
#endif

    Map<int,int> assump_map(-1);
    vec<Linear*> saved_constrs;
    vec<Lit> goal_ps;
    Minisat::vec<Lit> assump_ps;
    vec<Int> assump_Cs, goal_Cs, saved_constrs_Cs;
    vec<weight_t> sorted_assump_Cs;
    vec<Pair<Int, bool> > sum_sorted_soft_cls;
    bool    sat = false, weighted_instance = true;
    Lit assump_lit = lit_Undef, max_assump = lit_Undef;
    Int     try_lessthan = opt_goal, max_assump_Cs = Int_MIN;
    int     n_solutions = 0;    // (only for AllSolutions mode)
    vec<Pair<Lit,int> > psCs;
    vec<int8_t> multi_level_opt;
    bool opt_delay_init_constraints = false, 
         opt_core_minimization = (nClauses() > 0 || soft_cls.size() < 100000);
    IntLitQueue delayed_assump;
    Int delayed_assump_sum = 0;
    BitMap top_impl_gen(true);
    vec<Int> top_UB_stack;
    bool optimum_found = false;
    Lit last_unsat_constraint_lit = lit_Undef;

    Int LB_goalval = 0, UB_goalval = 0;    
    Sort::sort(&soft_cls[0], soft_cls.size(), LT<Pair<weight_t, Minisat::vec<Lit>*> >());
    int j = 0; Lit pj;
    for (int i = 0; i < soft_cls.size(); ++i) {
        soft_cls[i].fst /= goal_gcd;
        if (soft_cls[i].fst < 0) { 
            fixed_goalval += soft_cls[i].fst; soft_cls[i].fst = -soft_cls[i].fst; soft_cls[i].snd->last() = ~soft_cls[i].snd->last(); 
        }
        Lit p = soft_cls[i].snd->last();
        if (soft_cls[i].snd->size() == 1) p = ~p;
        if (value(p) != l_Undef) {
            if (value(p) == l_True) {
                fixed_goalval += soft_cls[i].fst;
                addUnit(p);
            } else {
                if (soft_cls[i].snd->size() > 1) sat_solver.addClause(*soft_cls[i].snd);
                addUnit(~p);
            }
        } else if (j > 0 && p == pj)  
            soft_cls[j-1].fst += soft_cls[i].fst;
        else if (j > 0 && p == ~pj) {
            fixed_goalval += (soft_cls[j-1].fst < soft_cls[i].fst ? soft_cls[j-1].fst : soft_cls[i].fst); 
            soft_cls[j-1].fst -= soft_cls[i].fst;
            if (soft_cls[j-1].fst < 0) soft_cls[j-1].fst = -soft_cls[j-1].fst, soft_cls[j-1].snd->last() = pj, pj = ~pj; 
        } else {
            if (j > 0 && soft_cls[j-1].fst == 0) j--;
            if (j < i) soft_cls[j] = soft_cls[i];
            pj = p; j++;
        }
    }
    if (j < soft_cls.size()) soft_cls.shrink(soft_cls.size() - j);
    top_for_strat = top_for_hard = soft_cls.size();
    if (soft_cls.size() > 0) Sort::sort(soft_cls);
    weighted_instance = (soft_cls.size() > 1 && soft_cls[0].fst != soft_cls.last().fst);
    for (int i = 0; i < soft_cls.size(); i++) {
        Lit p = soft_cls[i].snd->last();
        psCs.push(Pair_new(soft_cls[i].snd->size() == 1 ? p : ~p, i));
        if (weighted_instance) sorted_assump_Cs.push(soft_cls[i].fst);
        UB_goalval += soft_cls[i].fst;
    }
    LB_goalval += fixed_goalval, UB_goalval += fixed_goalval;
    Sort::sort(psCs);
    if (weighted_instance) Sort::sortUnique(sorted_assump_Cs);
    if (LB_goalvalue < LB_goalval) LB_goalvalue = LB_goalval;
    if (UB_goalvalue == Int_MAX)   UB_goalvalue = UB_goalval;
    else {
        for (int i = 0; i < psCs.size(); i++){
            goal_ps.push(~psCs[i].fst);
            goal_Cs.push(soft_cls[psCs[i].snd].fst);                                 
        }
        if (try_lessthan == Int_MAX) try_lessthan = ++UB_goalvalue;
        if (goal_ps.size() > 0) {
            addConstr(goal_ps, goal_Cs, try_lessthan - fixed_goalval, -2, assump_lit);
            convertPbs(false);
        }
    }
    if (opt_minimization != 1 || sorted_assump_Cs.size() == 0) {
        for (int i = 0; i < psCs.size(); i++){            
            assump_ps.push(psCs[i].fst);
            assump_Cs.push(Int(soft_cls[psCs[i].snd].fst));             
        }
        for (int i = 0; i < soft_cls.size(); i++) { 
            if (soft_cls[i].snd->size() > 1) sat_solver.addClause(*soft_cls[i].snd);
        }
        top_for_strat = top_for_hard = 0;
    } else {
        for (int i = soft_cls.size() - 1; i >= 0; i--) 
            for (int j = soft_cls[i].snd->size() - 1; j >= 0; j--) 
                sat_solver.setFrozen(var((*soft_cls[i].snd)[j]), true);
        Int sum = 0;
        int ml_opt = 0;
        vec<weight_t> sortedCs;
        multi_level_opt.push(false); sum_sorted_soft_cls.push(Pair_new(0, true));
        for (int i = 0, cnt = 0, sz = sorted_assump_Cs.size(), j = 1; j < sz; j++) {
            while (i < soft_cls.size() && soft_cls[i].fst < sorted_assump_Cs[j])
                sortedCs.push(soft_cls[i].fst), sum += soft_cls[i++].fst, cnt++;
            sum_sorted_soft_cls.push(Pair_new(sum, sum < sorted_assump_Cs[j]));
            multi_level_opt.push(sum < sorted_assump_Cs[j]);
            if (multi_level_opt.last()) ml_opt++;
        }
        extern void separationIndex(const vec<weight_t>& cs, vec<int>& separation_points);
        vec<int> gbmo_points; // generalized Boolean multilevel optimization points (GBMO)
        separationIndex(sortedCs, gbmo_points); // find GBMO
        for (int i = 0; i < gbmo_points.size(); i++) 
            multi_level_opt[bin_search(sorted_assump_Cs, sortedCs[gbmo_points[i]])] |= 2;
        if (gbmo_points.size() > 0 && opt_verbosity >= 1)
            reportf("Generalized BMO splitting point(s) found and can be used.\n");
        sortedCs.clear(); gbmo_points.clear();

        //opt_stratification(sorted_assump_Cs, sum_sorted_soft_cls);
        opt_lexicographic = (opt_output_top < 0); // true;
        if (opt_verbosity >= 1 && ml_opt > 0 && opt_output_top < 0) 
            reportf("Boolean multilevel optimization (BMO) can be done in %d point(s).%s\n", 
                    ml_opt, (opt_lexicographic ? "" : " Try -lex-opt option."));
        max_assump_Cs = do_stratification(sat_solver, sorted_assump_Cs, soft_cls, top_for_strat, assump_ps, assump_Cs);
    }
    if (psCs.size() > 0) max_assump = psCs.last().fst;
    if (opt_minimization == 1 && opt_maxsat_prepr) 
        preprocess_soft_cls(assump_ps, assump_Cs, max_assump, max_assump_Cs, delayed_assump, delayed_assump_sum);
    if (opt_verbosity >= 1)
        sat_solver.printVarsCls(goal_ps.size() > 0, &soft_cls, top_for_strat);
    if (opt_polarity_sug != 0) { 
        for (int i = 0; i < soft_cls.size(); i++){
            Lit p = soft_cls[i].snd->last(); if (soft_cls[i].snd->size() == 1) p = ~p;
            bool dir = opt_polarity_sug > 0 ? !sign(p) : sign(p);
            sat_solver.setPolarity(var(p), LBOOL(dir));
        }
    }
    bool first_time = false;
    int start_solving_cpu = cpuTime();
    if (opt_cpu_lim != INT32_MAX) {
        first_time=true; limitTime(start_solving_cpu + (opt_cpu_lim - start_solving_cpu)/4);
    }
// #ifdef USE_SCIP
//     reportf("scip\n");
//     extern bool opt_use_scip_slvr;
//     int sat_orig_vars = sat_solver.nVars(), sat_orig_cls = sat_solver.nClauses();
//     if (opt_use_scip_slvr)
//         scip_solve(&assump_ps, &assump_Cs, &delayed_assump, weighted_instance, sat_orig_vars, sat_orig_cls);
// #endif
    lbool status = l_Undef;

    if(opt_only_hards) {
        if (opt_verbosity > 0) reportf("Run SAT query with only hard clauses.\n");
        status = sat_solver.solveLimited(Minisat::vec<Lit>());
        opt_only_hards = false;
    }
    if(status == l_True){
        vec<bool> model;
        model.growTo(pb_n_vars, 0);
        Minisat::vec<Lit> soft_unsat;
        for (Var x = 0; x < pb_n_vars; x++)
            assert(sat_solver.modelValue(x) != l_Undef),
            model[x] = (sat_solver.modelValue(x) == l_True);
        
        for (int i = 0; i < top_for_strat; i++)
            if (soft_cls[i].snd->size() > 1)
                model[var(soft_cls[i].snd->last())] = !sign(soft_cls[i].snd->last());
        
        Int goalvalue = evalGoal(soft_cls, model, soft_unsat) + fixed_goalval;
        extern bool opt_satisfiable_out;
        if (
#ifdef USE_SCIP
            !SCIP_found_opt && 
#endif                
            (goalvalue < best_goalvalue || opt_output_top > 0 && goalvalue == best_goalvalue)) {
            best_goalvalue = goalvalue;
            model.moveTo(best_model);
            char* tmp = toString(best_goalvalue * goal_gcd);
            if (opt_satisfiable_out && opt_output_top < 0 && (opt_satlive || opt_verbosity == 0))
                printf("o %s\n", tmp), fflush(stdout);
            else if (opt_verbosity > 0 || !opt_satisfiable_out) 
                reportf("%s solution: %s\n", (optimum_found ? "Next" : "Found"), tmp);
            xfree(tmp);
        } else model.clear(); 
        if (best_goalvalue < UB_goalvalue && opt_output_top < 0) UB_goalvalue = best_goalvalue;
    }    
    while (1) {
    //   reportf("%d\n", cntr ++);
      if (use_base_assump) for (int i = 0; i < base_assump.size(); i++) assump_ps.push(base_assump[i]);
      if (opt_minimization == 1 && opt_to_bin_search && opt_unsat_conflicts >= 100000 &&
                                 sat_solver.conflicts < opt_unsat_conflicts - 500)
          sat_solver.setConfBudget(opt_unsat_conflicts - sat_solver.conflicts);
      else sat_solver.budgetOff();

      status = 
          base_assump.size() == 1 && base_assump[0] == assump_lit ? l_True :
          base_assump.size() == 1 && base_assump[0] == ~assump_lit ? l_False :
          sat_solver.solveLimited(assump_ps);
      if (use_base_assump and !first_time) {
          for (int i = 0; i < base_assump.size(); i++) {
              if (status == l_True && var(base_assump[i]) < pb_n_vars) addUnit(base_assump[i]);
              assump_ps.pop();
          }
          if (status != l_Undef) base_assump.clear();
      }
      if (first_time) { 
        first_time = false; sat_solver.clearInterrupt(); 
        if (asynch_interrupt && cpu_interrupt) asynch_interrupt = false;
        cpu_interrupt = false; limitTime(opt_cpu_lim);
        if (status == l_Undef) continue;
      }
      if (status  == l_Undef) {
        if (asynch_interrupt) { reportf("*** Interrupted ***\n"); break; }
        if (opt_minimization == 1 && opt_to_bin_search && sat_solver.conflicts >= opt_unsat_conflicts) goto SwitchSearchMethod;
      } else if (status == l_True) { // SAT returned
        //  reportf("SAT\n");
        if (opt_minimization == 1 && opt_delay_init_constraints) {
            opt_delay_init_constraints = false;
            convertPbs(false);
            constrs.clear();
            continue;
        }
        Int lastCs = 1;
        if(opt_minimization != 1 && assump_ps.size() == 1 && assump_ps.last() == assump_lit) {
          addUnit(assump_lit);
          lastCs = assump_Cs.last();
          assump_ps.pop(); assump_Cs.pop(); assump_lit = lit_Undef;
        }
        sat = true;

        if (cmd == sc_AllSolutions){
            Minisat::vec<Lit>    ban;
            n_solutions++;
            reportf("MODEL# %d:", n_solutions);
            for (Var x = 0; x < pb_n_vars; x++){
                assert(sat_solver.modelValue(x) != l_Undef);
                ban.push(mkLit(x, sat_solver.modelValue(x) == l_True));
                if (index2name[x][0] != '#')
                    reportf(" %s%s", (sat_solver.modelValue(x) == l_False)?"-":"", index2name[x]);
            }
            reportf("\n");
            sat_solver.addClause_(ban);
        }else{
            vec<bool> model;
            model.growTo(pb_n_vars, 0);
            Minisat::vec<Lit> soft_unsat;
            for (Var x = 0; x < pb_n_vars; x++)
                // assert(sat_solver.modelValue(x) != l_Undef),
                model[x] = (sat_solver.modelValue(x) == l_True);
            for (int i = 0; i < top_for_strat; i++)
                if (soft_cls[i].snd->size() > 1)
                    model[var(soft_cls[i].snd->last())] = !sign(soft_cls[i].snd->last());
            Int goalvalue = evalGoal(soft_cls, model, soft_unsat) + fixed_goalval;
            extern bool opt_satisfiable_out;
            if (
#ifdef USE_SCIP
                !SCIP_found_opt && 
#endif                
                    (goalvalue < best_goalvalue || opt_output_top > 0 && goalvalue == best_goalvalue)) {
                best_goalvalue = goalvalue;
                model.moveTo(best_model);
                char* tmp = toString(best_goalvalue * goal_gcd);
                if (opt_satisfiable_out && opt_output_top < 0 && (opt_satlive || opt_verbosity == 0))
                    printf("o %s\n", tmp), fflush(stdout);
                else if (opt_verbosity > 0 || !opt_satisfiable_out) 
                    reportf("%s solution: %s\n", (optimum_found ? "Next" : "Found"), tmp);
                xfree(tmp);
                // for(int x = 0; x < pb_n_vars; x ++)
                //     sat_solver.setPolarity(x, 1 - best_model[x]);
            } else model.clear(); 
            if (best_goalvalue < UB_goalvalue && opt_output_top < 0) UB_goalvalue = best_goalvalue;
            else if (opt_output_top > 1) {
                while (top_UB_stack.size() > 0 && top_UB_stack.last() < best_goalvalue) top_UB_stack.pop();
                if (top_UB_stack.size() == 0 || top_UB_stack.last() > best_goalvalue) top_UB_stack.push(best_goalvalue);
                if (top_UB_stack.size() >= opt_output_top) {
                    Int &bound = top_UB_stack[top_UB_stack.size() - opt_output_top];
                    if (bound < UB_goalvalue) UB_goalvalue = bound;
                }
            }
            if (cmd == sc_FirstSolution || (opt_minimization == 1 || UB_goalvalue == LB_goalvalue) &&
                                           sorted_assump_Cs.size() == 0 && delayed_assump.empty() && false) {
                if (opt_minimization == 1 && opt_output_top > 0) {
                    outputResult(*this, false);
                    if (opt_verbosity > 0 && !optimum_found) {
                        optimum_found = true;
                        char* tmp = toString(best_goalvalue * goal_gcd);
                        reportf(" OPT SOLUTION: %s\n", tmp);
                        xfree(tmp);
                    }
                    if (--opt_output_top == 0) break;
                    else { 
                        best_goalvalue = Int_MAX;
                        if (soft_unsat.size() > 0) sat_solver.addClause(soft_unsat);
                        else { status = l_False; break; }
                        for (int i = 0; i < soft_cls.size(); i++)
                            if (soft_unsat[i] == soft_cls[i].snd->last() && soft_cls[i].snd->size() > 1 && 
                                    top_impl_gen.at(var(soft_unsat[i]))) {
                                top_impl_gen.set(var(soft_unsat[i]), false);
                                for (int j = soft_cls[i].snd->size() - 2; j >= 0; j--)
                                    sat_solver.addClause(~soft_unsat[i], ~(*soft_cls[i].snd)[j]);
                            }
                        continue;
                    }
                } else break;
            }
            if (opt_minimization == 1) {
                assert(sorted_assump_Cs.size() > 0 || !delayed_assump.empty()); 
                int old_top = top_for_strat;
                if (delayed_assump.empty() || sorted_assump_Cs.size() > 0 && Int(sorted_assump_Cs.last()) > delayed_assump.top().fst) {
                    if (sorted_assump_Cs.size() > 0 && opt_lexicographic && multi_level_opt[sorted_assump_Cs.size()]) {
                        bool standard_multi_level_opt = multi_level_opt[sorted_assump_Cs.size()] & 1;
                        bool general_multi_level_opt = multi_level_opt[sorted_assump_Cs.size()] & 2;
                        Int bound = sum_sorted_soft_cls[sorted_assump_Cs.size()].fst + delayed_assump_sum;
                        int cnt_assump = 0;
                        if (general_multi_level_opt && assump_ps.last() == last_unsat_constraint_lit)
                            addUnit(assump_ps.last()), assump_Cs.last() = -assump_Cs.last(), cnt_assump++;
                        if (standard_multi_level_opt)
                            for (int i = 0; i < assump_ps.size() && assump_ps[i] <= max_assump; i++)
                                if (assump_Cs[i] > bound)
                                    addUnit(assump_ps[i]), assump_Cs[i] = -assump_Cs[i], cnt_assump++;
                        if (cnt_assump > 0) {
                            clear_assumptions(assump_ps, assump_Cs);
                            if (opt_verbosity > 0) reportf("BMO - done.\n");
                        }
                    }
                    if(sorted_assump_Cs.size() > 0)
                        max_assump_Cs = do_stratification(sat_solver, sorted_assump_Cs, soft_cls, top_for_strat, assump_ps, assump_Cs);
                } else {
                    max_assump_Cs = delayed_assump.top().fst;
                    vec<Pair<Lit, Int> > new_assump;
                    do { 
                        new_assump.push(Pair_new(delayed_assump.top().snd, max_assump_Cs));
                        delayed_assump_sum -= delayed_assump.top().fst;
                        delayed_assump.pop(); 
                    } while (!delayed_assump.empty() && delayed_assump.top().fst >= max_assump_Cs);
                    Sort::sort(new_assump); int sz = new_assump.size();
                    assump_ps.growTo(assump_ps.size() + sz); assump_Cs.growTo(assump_Cs.size() + sz);
                    for (int i = assump_ps.size() - 1; i >= sz; i--)
                        assump_ps[i] = assump_ps[i-sz], assump_Cs[i] = assump_Cs[i-sz];
                    for (int fr = sz, to = 0, i = 0; i < new_assump.size(); i++) {
                        Lit p = new_assump[i].fst;
                        while (fr < assump_ps.size() && assump_ps[fr] <= p)
                            assump_ps[to] = assump_ps[fr], assump_Cs[to++] = assump_Cs[fr++];
                        assump_ps[to] = p; assump_Cs[to++] = new_assump[i].snd;
                    }
                }
                harden_soft_cls(assump_ps, assump_Cs, sorted_assump_Cs, delayed_assump, delayed_assump_sum);
                if (top_for_strat < old_top) {
                    try_lessthan = best_goalvalue;
                    if (opt_maxsat_prepr) 
                        preprocess_soft_cls(assump_ps, assump_Cs, max_assump, max_assump_Cs, delayed_assump, delayed_assump_sum);
                }
                continue;
            } else harden_soft_cls(assump_ps, assump_Cs, sorted_assump_Cs, delayed_assump, delayed_assump_sum);
            if (opt_minimization == 0 || best_goalvalue - LB_goalvalue < opt_seq_thres) {
                opt_minimization = 0;
                assump_lit = (assump_ps.size() == 0 ? lit_Undef : mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true));
                try_lessthan = best_goalvalue;
            } else {
                assump_lit = assump_lit == lit_Undef || !use_base_assump ?
                    mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars)) : assump_lit;
                try_lessthan = (LB_goalvalue*(100-opt_bin_percent) + best_goalvalue*(opt_bin_percent))/100;
            }
            Int goal_diff = harden_goalval+fixed_goalval;
            if (!addConstr(goal_ps, goal_Cs, try_lessthan - goal_diff, -2, assump_lit))
                break; // unsat
            if (assump_lit != lit_Undef && !use_base_assump) {
                sat_solver.setFrozen(var(assump_lit),true);
                assump_ps.push(assump_lit), assump_Cs.push(opt_minimization == 2 ? try_lessthan : lastCs);
            }
            last_unsat_constraint_lit = lit_Undef;
            convertPbs(false);
        }
      } else { // UNSAT returned
        if (assump_ps.size() == 0 && assump_lit == lit_Undef || 
            opt_minimization == 0 && sat_solver.conflict.size() == 1 && sat_solver.conflict[0] == ~assump_lit) break;
        {
        Minisat::vec<Lit> core_mus;
        if (opt_core_minimization) {
            if (weighted_instance) {
                vec<Pair<Pair<Int, int>, Lit> > Cs_mus;
                for (int i = 0; i < sat_solver.conflict.size(); i++) {
                    Lit p = ~sat_solver.conflict[i];
                    int j = bin_search(assump_ps, p);
                    Cs_mus.push(Pair_new(Pair_new((j>=0 ? assump_Cs[j] : 0),i),p));
                }
                Sort::sort(Cs_mus);
                for (int i = 0; i < Cs_mus.size(); i++) core_mus.push(Cs_mus[i].snd);
            } else
                for (int i = 0; i < sat_solver.conflict.size(); i++) core_mus.push(~sat_solver.conflict[i]);
            core_minimization(sat_solver, core_mus);
        } else
            for (int i = 0; i < sat_solver.conflict.size(); i++) core_mus.push(sat_solver.conflict[i]);
        if (core_mus.size() > 0 && core_mus.size() < 6) sat_solver.addClause(core_mus);
        Int min_removed = Int_MAX, min_bound = Int_MAX;
        int removed = 0;
        bool other_conflict = false;

        if (opt_minimization == 1) { 
            goal_ps.clear(); goal_Cs.clear();
        }
        for (int j, i = 0; i < core_mus.size(); i++) {
            Lit p = ~core_mus[i];
            if ((j = bin_search(assump_ps, p)) >= 0) { 
                if (opt_minimization == 1 || p <= max_assump) {
                    goal_ps.push(~p), goal_Cs.push(opt_minimization == 1 ? 1 : assump_Cs[j]);
                    if (assump_Cs[j] < min_removed) min_removed = assump_Cs[j];
                } else { 
                    other_conflict = true;
                    if (assump_Cs[j] < min_bound) min_bound = assump_Cs[j];
                }
                assump_Cs[j] = -assump_Cs[j]; removed++;
            }
        }
        if (other_conflict && min_removed != Int_MAX && opt_minimization != 1) min_removed = 0;
        vec<int> modified_saved_constrs;
        if (removed > 0) {
            int j = 0;
            for (int i = 0; i < assump_ps.size(); i++) {
                if (assump_Cs[i] < 0) {
                    Minisat::Lit p = assump_ps[i];
                    if (opt_minimization == 1 && p > max_assump) { // && assump_Cs[i] == -min_removed) {
                        int k = assump_map.at(toInt(p));
                        if (k >= 0 && k < saved_constrs.size() &&  saved_constrs[k] != NULL && saved_constrs[k]->lit == p) {
                            if (saved_constrs[k]->lo != Int_MIN && saved_constrs[k]->lo > 1 || 
                                    saved_constrs[k]->hi != Int_MAX && saved_constrs[k]->hi < saved_constrs[k]->size - 1) {
                                if (saved_constrs[k]->lo != Int_MIN) --saved_constrs[k]->lo; else ++saved_constrs[k]->hi;
                                constrs.push(saved_constrs[k]); 
                                constrs.last()->lit = lit_Undef;
                                modified_saved_constrs.push(k);
                            } else { saved_constrs[k]->~Linear(); saved_constrs[k] = NULL; }
                            assump_map.set(toInt(p), -1);
                        }
                    }
                    if (assump_Cs[i] == -min_removed || opt_minimization != 1) continue;
                    assump_Cs[i] = -min_removed - assump_Cs[i];
                    if (opt_minimization == 1 &&  assump_Cs[i] < max_assump_Cs ) {
                        delayed_assump.push(Pair_new(assump_Cs[i], assump_ps[i]));
                        delayed_assump_sum += assump_Cs[i];
                        continue;
                    }
                }
                if (j < i) assump_ps[j] = assump_ps[i], assump_Cs[j] = assump_Cs[i];
                j++;
            }
            if ((removed = assump_ps.size() - j) > 0)
                assump_ps.shrink(removed), assump_Cs.shrink(removed);
            if (min_bound == Int_MAX || min_bound < LB_goalvalue) min_bound = LB_goalvalue + 1;
            LB_goalvalue = (min_removed == 0 ? next_sum(LB_goalvalue - fixed_goalval - harden_goalval, goal_Cs) + fixed_goalval + harden_goalval: 
                            min_removed == Int_MAX ? min_bound : LB_goalvalue + min_removed);
        } else if (opt_minimization == 1) LB_goalvalue = next_sum(LB_goalvalue - fixed_goalval - harden_goalval, goal_Cs) + fixed_goalval + harden_goalval; 
        else LB_goalvalue = try_lessthan;

        if (LB_goalvalue == best_goalvalue && opt_minimization != 1) break;

        Int goal_diff = harden_goalval+fixed_goalval;
        if (opt_minimization == 1) {
            assump_lit = lit_Undef;
            try_lessthan = goal_diff + 2;
	} else if (opt_minimization == 0 || best_goalvalue == Int_MAX || best_goalvalue - LB_goalvalue < opt_seq_thres) {
            if (best_goalvalue != Int_MAX) opt_minimization = 0;
            assump_lit = (assump_ps.size() == 0 ? lit_Undef : mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true));
	    try_lessthan = (best_goalvalue != Int_MAX ? best_goalvalue : UB_goalvalue+1);
	} else {
            assump_lit = assump_lit == lit_Undef || !use_base_assump ?
                mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars)) : assump_lit;
	    try_lessthan = (LB_goalvalue*(100-opt_bin_percent) + best_goalvalue*(opt_bin_percent))/100;
	}
        if (!addConstr(goal_ps, goal_Cs, try_lessthan - goal_diff, -2, assump_lit))
            break; // unsat
        if (constrs.size() > 0 && (opt_minimization != 1 || !opt_delay_init_constraints)) {
            convertPbs(false);
            if (opt_minimization == 1) {
                if (constrs.size() == modified_saved_constrs.size() + 1) assump_lit = constrs.last()->lit;
                for (int i = 0, j = 0; i < modified_saved_constrs.size(); i++) {
                    int k = modified_saved_constrs[i];
                    Lit newp = constrs[j++]->lit;
                    sat_solver.setFrozen(var(newp),true);
                    sat_solver.addClause(~saved_constrs[k]->lit, newp);
                    saved_constrs[k]->lit = newp;
                    assump_ps.push(newp); assump_Cs.push(saved_constrs_Cs[k]);
                    if (saved_constrs[k]->lo > 1 || saved_constrs[k]->hi < saved_constrs[k]->size - 1)
                        assump_map.set(toInt(newp), k);
                }
                modified_saved_constrs.clear();
            }
        }
        if (assump_lit != lit_Undef && !use_base_assump) {
            sat_solver.setFrozen(var(assump_lit),true);
            assump_ps.push(assump_lit); assump_Cs.push(opt_minimization == 2 ? try_lessthan : 
                                                       min_removed != Int_MAX && min_removed != 0 ? min_removed : 1);
        }
        last_unsat_constraint_lit = lit_Undef;
        if (opt_minimization == 1) {
            last_unsat_constraint_lit = assump_lit;
            if (constrs.size() > 0 && constrs.last()->lit == assump_lit) {
                Minisat::vec<Lit> new_assump; 
                if (constrs.size() > 1) constrs[0] = constrs.last(), constrs.shrink(constrs.size() - 1);
                optimize_last_constraint(constrs, assump_ps, new_assump);
                if (new_assump.size() > 0) {
                    delayed_assump_sum += Int(new_assump.size()) * assump_Cs.last();
                    for (int i=0; i < new_assump.size(); i++) 
                        delayed_assump.push(Pair_new(assump_Cs.last(), new_assump[i]));
                }
                if (constrs.last()->lit != assump_lit) assump_lit = assump_ps.last() = constrs.last()->lit;
                saved_constrs.push(constrs.last()), assump_map.set(toInt(assump_lit),saved_constrs.size() - 1);
                saved_constrs_Cs.push(assump_Cs.last());
            } else if (goal_ps.size() > 1) {
                saved_constrs.push(new (mem.alloc(sizeof(Linear) + goal_ps.size()*(sizeof(Lit) + sizeof(Int))))
                        Linear(goal_ps, goal_Cs, Int_MIN, 1, assump_lit));
                assump_map.set(toInt(assump_lit),saved_constrs.size() - 1);
                saved_constrs_Cs.push(assump_Cs.last());
            }
            if (!opt_delay_init_constraints) {
                int j = 0;
                for (int i = 0; i < saved_constrs.size(); i++)
                    if (saved_constrs[i] != NULL) {
                        if (saved_constrs[i]->lo == 1 && saved_constrs[i]->hi == Int_MAX || 
                                saved_constrs[i]->hi == saved_constrs[i]->size - 1 && saved_constrs[i]->lo == Int_MIN ) {
                            saved_constrs[i]->~Linear();
                            saved_constrs[i] = NULL;
                        } else {
                            if (j < i) {
                                saved_constrs[j] = saved_constrs[i],  saved_constrs[i] = NULL, saved_constrs_Cs[j] = saved_constrs_Cs[i];
                                if (saved_constrs[j]->lit != lit_Undef) assump_map.set(toInt(saved_constrs[j]->lit), j); 
                            }
                            j++;
                        }
                    }
                if (j < saved_constrs.size()) 
                    saved_constrs.shrink(saved_constrs.size() - j), saved_constrs_Cs.shrink(saved_constrs_Cs.size() - j);
                constrs.clear();
            }
        }
        }
        if (weighted_instance && sat && sat_solver.conflicts > 10000)
            harden_soft_cls(assump_ps, assump_Cs, sorted_assump_Cs, delayed_assump, delayed_assump_sum);
        if (opt_minimization >= 1 && opt_verbosity >= 2) {
            char *t; reportf("Lower bound  = %s, assump. size = %d, stratif. level = %d (cls: %d, wght: %s)\n", t=toString(LB_goalvalue * goal_gcd), 
                    assump_ps.size(), sorted_assump_Cs.size(), top_for_strat, toString(sorted_assump_Cs.size() > 0 ? sorted_assump_Cs.last() : 0)); xfree(t); }
        if (opt_minimization == 2 && opt_verbosity == 1 && use_base_assump) {
            char *t; reportf("Lower bound  = %s\n", t=toString(LB_goalvalue * goal_gcd)); xfree(t); }
SwitchSearchMethod:        
        if (opt_minimization == 1 && opt_to_bin_search && LB_goalvalue + 5 < UB_goalvalue &&
            cpuTime() >= opt_unsat_cpu + start_solving_cpu && sat_solver.conflicts > opt_unsat_conflicts) {
            int cnt = 0;
            for (int j = 0, i = 0; i < psCs.size(); i++) {
                const Int &w = soft_cls[psCs[i].snd].fst;
                if (j == assump_ps.size() || psCs[i].fst < assump_ps[j] || psCs[i].fst == assump_ps[j] && w > assump_Cs[j])
                    if (++cnt >= 50000) { opt_to_bin_search = false; break; }
                if (j < assump_ps.size() && psCs[i].fst == assump_ps[j]) j++;
            }
            if (opt_to_bin_search) {
                // reportf("BIN\n");
                for (int i = assump_ps.size() - 1; i >= 0 && assump_ps[i] > max_assump; i--)
                    assump_ps.pop(), assump_Cs.pop();
                goal_ps.clear(); goal_Cs.clear();
                bool clear_assump = (cnt * 3 >= assump_ps.size()); use_base_assump = clear_assump;
                Int sumCs(0);
                int k = 0;
                for (int j = 0, i = 0; i < psCs.size(); i++) {
                    const Lit p = psCs[i].fst;
                    const Int &w = soft_cls[psCs[i].snd].fst;
                    bool in_harden = harden_lits.has(p);
                    if ((j == assump_ps.size() || p < assump_ps[j] || 
                            p == assump_ps[j] && (clear_assump || w > assump_Cs[j] || in_harden)) &&
                        (!in_harden || harden_lits.at(p) < w))
                            goal_ps.push(~p), goal_Cs.push(in_harden ? w - harden_lits.at(p) : w), 
                                sumCs += goal_Cs.last();
                    if (j < assump_ps.size() && p == assump_ps[j]) {
                        if (!clear_assump && w == assump_Cs[j] && !in_harden) { 
                            if (k < j) assump_ps[k] = assump_ps[j], assump_Cs[k] = assump_Cs[j];
                            k++;
                        }
                        j++;
                    }
                }
                if (k < assump_ps.size()) assump_ps.shrink(assump_ps.size() - k), assump_Cs.shrink(assump_Cs.size() - k);
                for (int i = 0; i < top_for_strat; i++) { 
                    if (soft_cls[i].snd->size() > 1) sat_solver.addClause(*soft_cls[i].snd);
                }
                for (int i = 0; i < am1_rels.size(); i++) 
                    goal_ps.push(~am1_rels[i].fst), goal_Cs.push(am1_rels[i].snd), sumCs += goal_Cs.last();
                {   Int lower_bound = LB_goalvalue-fixed_goalval-harden_goalval; int j = 0;
                    for (int i = 0; i < goal_Cs.size(); i++)
                        if (sumCs - goal_Cs[i] < lower_bound) {
                            if (!harden_lits.has(goal_ps[i])) top_for_hard--;
                            addUnit(goal_ps[i]), harden_goalval += goal_Cs[i];
                        } else { if (j < i) goal_ps[j] = goal_ps[i], goal_Cs[j] = goal_Cs[i]; j++; }
                    if (j < goal_ps.size()) goal_ps.shrink(goal_ps.size() - j), goal_Cs.shrink(goal_Cs.size() - j);
                }
                top_for_strat = 0; sorted_assump_Cs.clear(); am1_rels.clear(); harden_lits.clear();
                delayed_assump.clear(); delayed_assump_sum = 0;
                if (opt_verbosity >= 1) {
                    reportf("Switching to binary search ... (after %g s and %d conflicts) with %d goal literals and %d assumptions\n", 
                            cpuTime(), sat_solver.conflicts, goal_ps.size(), assump_ps.size());
                }
                opt_minimization = 2;
                if (assump_ps.size() == 0) opt_reuse_sorters = false;
                if (opt_convert_goal != ct_Undef) opt_convert = opt_convert_goal;
                if (sat) {
                    try_lessthan = best_goalvalue; 
                    assump_lit = (assump_ps.size() == 0 && !use_base_assump ? lit_Undef : 
                                                          mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true));
                    if (assump_lit != lit_Undef && !use_base_assump) assump_ps.push(assump_lit), assump_Cs.push(try_lessthan);
                    if (!addConstr(goal_ps, goal_Cs, try_lessthan - fixed_goalval - harden_goalval, -2, assump_lit))
                        break; // unsat
                    if (constrs.size() > 0) convertPbs(false);
                }
            }
        }
      }         
    } // END OF LOOP

    if (status == l_False && opt_output_top > 0) printf("v\n");
    if (goal_gcd != 1) {
        if (best_goalvalue != Int_MAX) best_goalvalue *= goal_gcd;
        if (LB_goalvalue   != Int_MIN) LB_goalvalue *= goal_gcd;
        if (UB_goalvalue   != Int_MAX) UB_goalvalue *= goal_gcd;
    }
    if (opt_verbosity >= 1 && opt_output_top < 0){
        if      (!sat)
            reportf(asynch_interrupt ? "\bUNKNOWN\b\n" : "\bUNSATISFIABLE\b\n");
        else if (soft_cls.size() == 0 && best_goalvalue == INT_MAX)
            reportf("\bSATISFIABLE: No goal function specified.\b\n");
        else if (cmd == sc_FirstSolution){
            char* tmp = toString(best_goalvalue);
            reportf("\bFirst solution found: %s\b\n", tmp);
            xfree(tmp);
        } else if (asynch_interrupt){
            extern bool opt_use_maxpre;
            char* tmp = toString(best_goalvalue);
            if (!opt_use_maxpre) reportf("\bSATISFIABLE: Best solution found: %s\b\n", tmp);
            xfree(tmp);
       } else
#ifdef USE_SCIP
           if (!SCIP_found_opt)
#endif
       {
            char* tmp = toString(best_goalvalue);
            reportf("\bOptimal solution: %s\b\n", tmp);
            xfree(tmp);
       }
    }
}

int lower_bound(vec<Lit>& set, Lit elem)
{
    int count = set.size(), fst = 0, step, it;
    while (count > 0) {
        step = count / 2; it = fst + step;
        if (set[it] < elem) fst = ++it, count -= step + 1;
        else count = step;
    }
    return fst;
}

void set_difference(vec<Lit>& set1, const vec<Lit>& set2)
{
    int j, k = 0, n1 = set1.size(), n2 = set2.size();
    if (n2 == 0) return;
    if (n2 == 1) {
        j = n1;
        if ((k=bin_search(set1, set2[0])) >= 0)
            memmove(&set1[k], &set1[k+1], sizeof(Lit)*(n1 - k - 1)), j--;
    } else {
        Lit *it2 = (Lit *)&set2[0], *fin2 = it2 + n2;
        Lit *ok1 = (Lit *)&set1[0] + lower_bound(set1, *it2);
        Lit *it1 = ok1, *fwd = ok1, *fin1 = (Lit *)&set1[0] + n1;
        while (fwd < fin1) {
            while (it2 < fin2 && *it2 < *fwd) it2++;
            if (it2 < fin2) {
                while (fwd < fin1 && *fwd < *it2) fwd++;
                if (fwd >= fin1 || *fwd == *it2) {
                    if (ok1 < it1) memmove(ok1, it1, sizeof(Lit)*(fwd - it1));
                    ok1 += fwd - it1; it1 = ++fwd; it2++;
                } 
            } else { 
                if (ok1 < it1) memmove(ok1, it1, sizeof(Lit)*(fin1 - it1)); 
                ok1 += fin1 - it1; break; 
            }
        }
        j = ok1 - &set1[0];
    }
    if (j < n1) set1.shrink(n1 - j);
}

struct mapLT { Map<Lit, vec<Lit>* >&c; bool operator()(Lit p, Lit q) { return c.at(p)->size() < c.at(q)->size(); }};

void MsSolver::preprocess_soft_cls(Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs, const Lit max_assump, const Int& max_assump_Cs, 
                                              IntLitQueue& delayed_assump, Int& delayed_assump_sum)
{
    Map<Lit, vec<Lit>* > conns;
    vec<Lit> conns_lit;
    vec<Lit> confl;
    vec<Lit> lits;
    for (int i = 0; i < assump_ps.size() && assump_ps[i] <= max_assump; i++) {
        Minisat::vec<Lit> props;
        Lit assump = assump_ps[i];
        if (sat_solver.prop_check(assump, props))
            for (int l, j = 0; j < props.size(); j++) {
                if ((l = bin_search(assump_ps,  ~props[j])) >= 0 && assump_ps[l] <= max_assump) {
                    if (!conns.has(assump)) conns.set(assump,new vec<Lit>());
                    conns.ref(assump)->push(~props[j]);
                    if (!conns.has(~props[j])) conns.set(~props[j], new vec<Lit>());
                    conns.ref(~props[j])->push(assump);
                }
            }  
        else confl.push(assump);
    }
    conns.domain(conns_lit);
    if (confl.size() > 0) {
        for (int i = 0; i < conns_lit.size(); i++) {
            if (bin_search(confl, conns_lit[i]) >= 0) {
                delete conns.ref(conns_lit[i]);
                conns.exclude(conns_lit[i]);
            } else {
                vec<Lit>& dep_lit = *conns.ref(conns_lit[i]);
                Sort::sortUnique(dep_lit);
                set_difference(dep_lit, confl);
                if (dep_lit.size() == 0) { delete conns.ref(conns_lit[i]); conns.exclude(conns_lit[i]); }
                else lits.push(conns_lit[i]);
            }
        }
        conns_lit.clear(); conns.domain(conns_lit);
        for (int l, i = 0; i < confl.size(); i++) {
            Lit p = confl[i];
            if ((l = bin_search(assump_ps, p)) >= 0 && assump_ps[l] <= max_assump) {
                if (!harden_lits.has(p)) harden_lits.set(p, assump_Cs[l]); else harden_lits.ref(p) += assump_Cs[l];
                harden_goalval += assump_Cs[l];
                addUnit(~p); LB_goalvalue += assump_Cs[l]; assump_Cs[l] = -assump_Cs[l];
            }
        }
        if (opt_verbosity >= 2) reportf("Found %d Unit cores\n", confl.size());
    } else
        for (int i = 0; i < conns_lit.size(); i++) { 
            lits.push(conns_lit[i]); 
            Sort::sortUnique(*conns.ref(conns_lit[i])); 
        }
    Sort::sort(lits);
    mapLT cmp {conns};
    int am1_cnt = 0, am1_len_sum = 0;
    //for (int i = 100000; i > 0 && lits.size() > 0; i--) {
    while (lits.size() > 0) {
        vec<Lit> am1;
        Lit minl = lits[0];
        for (int new_sz,  sz = conns.at(minl)->size(), i = 1; i < lits.size(); i++)
            if ((new_sz = conns.at(lits[i])->size()) < sz) minl = lits[i], sz = new_sz;
        am1.push(minl);
        vec<Lit>& dep_minl = *conns.ref(minl);
        Sort::sort(dep_minl, cmp);
        for (int sz = dep_minl.size(), i = 0; i < sz; i++) {
            Lit l = dep_minl[i];
            if (bin_search(lits, l) >= 0) {
                int i;
                const vec<Lit>& dep_l = *conns.at(l);
                for (i = 1; i < am1.size() && bin_search(dep_l, am1[i]) >= 0; ++i);
                if (i == am1.size()) am1.push(l);
            }
        }
        Sort::sort(dep_minl);
        Sort::sort(am1);
        set_difference(lits, am1);
        for (int i = 0; i < conns_lit.size(); i++)  set_difference(*conns.ref(conns_lit[i]), am1);
        if (am1.size() > 1) {
            Minisat::vec<Lit> cls;
            vec<int> ind;
            Int min_Cs = Int_MAX;
            for (int l, i = 0; i < am1.size(); i++)
                if ((l = bin_search(assump_ps, am1[i])) >= 0 && assump_Cs[l] > 0) {
                    ind.push(l);
                    if (assump_Cs[l] < min_Cs) min_Cs = assump_Cs[l];
                }
                else reportf("am1: %d %d %d %d %s\n", i, am1.size(), toInt(am1[0]), toInt(am1[i]), (l>=0 && l <assump_Cs.size()?toString(assump_Cs[l]):"???"));
            if (ind.size() < 2) continue;
            for (int i = 0; i < ind.size(); i++) {
                if (assump_Cs[ind[i]] == min_Cs) cls.push(assump_ps[ind[i]]), assump_Cs[ind[i]] = -assump_Cs[ind[i]];
                else {
                    cls.push(assump_ps[ind[i]]); //~r);
                    assump_Cs[ind[i]] -= min_Cs;
                    if (assump_Cs[ind[i]] < max_assump_Cs) {
                        delayed_assump.push(Pair_new(assump_Cs[ind[i]], assump_ps[ind[i]]));
                        delayed_assump_sum += assump_Cs[ind[i]];
                        assump_Cs[ind[i]] = - assump_Cs[ind[i]];
                    }
                }
                if (!harden_lits.has(assump_ps[ind[i]])) harden_lits.set(assump_ps[ind[i]], min_Cs);
                else harden_lits.ref(assump_ps[ind[i]]) += min_Cs;
            }
            Lit r = mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true);
            sat_solver.setFrozen(var(r), true);
            cls.push(~r); assump_ps.push(r); assump_Cs.push(min_Cs);
            am1_rels.push(Pair_new(r,min_Cs));
            sat_solver.addClause(cls);
            if (ind.size() > 2) min_Cs = Int(ind.size() - 1) * min_Cs;
            am1_cnt++; am1_len_sum += am1.size();  LB_goalvalue += min_Cs; harden_goalval += min_Cs;
        }
    }
    if (am1_cnt > 0 || confl.size() > 0) clear_assumptions(assump_ps, assump_Cs);
    if (opt_verbosity >= 2 && am1_cnt > 0) 
        reportf("Found %d AtMostOne cores of avg size: %.2f\n", am1_cnt, (double)am1_len_sum/am1_cnt);
}

