/**************************************************************************************[MsSolver.h ]
  Copyright (c) 2018-2019, Marek Piotrów

  Based on PbSolver.h ( Copyright (c) 2005-2010, Niklas Een, Niklas Sorensson)

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

#ifndef MsSolver_h
#define MsSolver_h

#include "PbSolver.h"

Int evalGoal(const vec<Pair<weight_t, Minisat::vec<Lit>* > >& soft_cls, 
  vec<bool>& model, Minisat::vec<Lit>& soft_unsat);

static inline int hleft (int i)  { return i * 2; }
static inline int hright(int i)  { return i * 2 + 1; }
static inline int hparent(int i) { return i / 2; }

class IntLitQueue {
  private:
    vec<Pair<Int, Lit> > heap;

    bool cmp(int x, int y) { 
        return heap[x].fst > heap[y].fst /*|| heap[x].fst == heap[y].fst && heap[x].snd > heap[y].snd*/; }

  public:
    IntLitQueue() { heap.push(Pair_new(1, lit_Undef)); }

    bool empty() { return heap.size() <= 1; }

    int size() { return heap.size(); }

    const vec<Pair<Int, Lit> >& getHeap() const { return heap; }

    void clear() { heap.shrink(heap.size() - 1); }

    const Pair<Int, Lit>& top() { return heap[1]; }

    void push(Pair<Int, Lit> p) { 
        heap.push();
        int i = heap.size() - 1;
        heap[0] = std::move(p);
        while (hparent(i) != 0 && cmp(0, hparent(i))) { // percolate up
            heap[i] = std::move(heap[hparent(i)]);
            i       = hparent(i);
        }
        heap[i] = std::move(heap[0]);
    }

    void pop(void) {
        heap[1] = std::move(heap.last());
        heap.pop();
        if (heap.size() > 1) { // percolate down
            int i = 1;
            heap[0] = std::move(heap[1]);
            while (hleft(i) < heap.size()){
                int child = hright(i) < heap.size() && cmp(hright(i), hleft(i)) ? hright(i) : hleft(i);
                if (!cmp(child, 0)) break;
                heap[i] = std::move(heap[child]);
                i       = child;
            }
            heap[i] = std::move(heap[0]);
        }
    }

} ;

#ifdef USE_SCIP
//#include <vector>
//#include <algorithm>
#include <scip/scip.h>
#include <scip/scipdefplugins.h>
#endif


class MsSolver : public PbSolver {
  public:
    MsSolver(bool use_preprocessing = false) : 
          PbSolver(use_preprocessing)
        , harden_goalval(0)
        , fixed_goalval(0)
        , goal_gcd(1)      {}

    Int                 harden_goalval,  //  Harden goalval used in the MaxSAT preprocessing 
                        fixed_goalval;   // The sum of weights of soft clauses that must be false
    vec<Pair<weight_t, Minisat::vec<Lit>* > > orig_soft_cls; // Soft clauses before preprocessing by MaxPre; empty if MaxPre is not used
    vec<Pair<weight_t, Minisat::vec<Lit>* > > soft_cls; // Relaxed non-unit soft clauses with weights; a relaxing var is the last one in a vector. 
    vec<Pair<weight_t, Minisat::vec<Lit>* > > all_cls; // All original clauses for incomplete methods. 
    vec<vec<int>*> lits_in_clauses; // Indexes of clauses where occur the literals. 
    vec<int> mentioned_lits; // The last clause index with the given literal. Live updating when adding new clauses to remove duplicates.

    weight_t            goal_gcd; // gcd of soft_cls weights
    int                 top_for_strat, top_for_hard; // Top indices to soft_cls for stratification and hardening operations.
    int                 soft_longs = 0;
    Map<Lit, Int>       harden_lits;    // The weights of literals included into "At most 1" clauses (MaxSAT preprocessing of soft clauese).
    vec<Pair<Lit,Int> > am1_rels;       // The weights of relaxing vars in "At most 1" clauses

    void    storeSoftClause(const vec<Lit>& ps, weight_t weight) {  
                Minisat::vec<Lit> *ps_copy = new Minisat::vec<Lit>; 
                for (int i = 0; i < ps.size(); i++) ps_copy->push(ps[i]);                   
                soft_cls.push(Pair_new(weight, ps_copy));
                if (ps.size() > 1) soft_longs ++; }   

    void    storeNonDuplicatedClause(const vec<Lit>& ps, weight_t weight){
                Minisat::vec<Lit> *ps_with_no_duplicates = new Minisat::vec<Lit>; 
                for (int i = 0; i < ps.size(); i++) {
                  int i_lit = toInt(ps[i]);
                  if(weight < 0 or (i + 1 != ps.size() or i == 0)) {
                    if(mentioned_lits[i_lit] == all_cls.size()) continue;
                    mentioned_lits[i_lit] = all_cls.size();                    
                  }
                  ps_with_no_duplicates->push(ps[i]);                   
                }
                all_cls.push(Pair_new(weight, ps_with_no_duplicates)); }   

    void    harden_soft_cls(Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs, vec<weight_t>& sorted_assump_Cs, IntLitQueue& delayed_assump, Int& delayed_assump_sum);
    void    optimize_last_constraint(vec<Linear*>& constrs, Minisat::vec<Lit>& assump_ps, Minisat::vec<Lit>& new_assump);

#ifdef USE_SCIP
    bool scip_solve(const Minisat::vec<Lit> *assump_ps, const vec<Int> *assump_Cs, const IntLitQueue *delayed_assump,
            bool weighted_instance, int sat_orig_vars, int sat_orig_cls);
#endif    

    bool    find_initial_solution();
    void    value_cl(vec<int>& unvalued, vec<bool>& model, vec<bool>& value_set, int& cl);
    void    unit_propagation(vec<bool>& model, int& hards);
    void    decimation_with_unit_propagation(vec<bool>& model, int& hards);
    bool    first_sat_based_model(vec<bool>& model, int& hards);
    bool    SatLike(bool one_run, int tl);
    void    before_SATLike();
    void    maxsat_solve(solve_Command cmd = sc_Minimize); 
    void    preprocess_soft_cls(Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs, const Lit max_assump, const Int& max_assump_Cs, 
                                           IntLitQueue& delayed_assump, Int& delayed_assump_sum);
/////////////////////////////////////////////////////////////////////////////////////
    int     hards = -1; // number of hard clauses
    void     set_lits_in_clauses();

    void    value_hard_clause(vec<int>& unvalued_lits, vec<bool>& model, vec<bool>& set_vars, int& c);
    void    run_up(vec<bool>& model, const int& H);

    bool    run_dist(const int& time_limit);
    bool    run_satlike(bool only_hards, const int& time_limit);

    bool    start_incomplete();

    void increasePointerList(vec<int>& elems, vec<int>& idx, int& cnt, int e){
        elems[cnt] = e;
        idx[e] = cnt  ++;
    }
    void decreasePointerList(vec<int>& elems, vec<int>& idx, int& cnt, int e){
        int i = idx[e];
        elems[i] = elems[cnt - 1];
        idx[elems[i]] = i;
        cnt --;
    }
} ;
class Metrics{
    public:
        int V, A, H;
        Metrics(int v, int a, int h){
            V = v;
            A = a;
            H = h;
        }
        void increasePointerList(vec<int>& elems, vec<int>& idx, int& cnt, int e){
            elems[cnt] = e;
            idx[e] = cnt  ++;
        }
        void decreasePointerList(vec<int>& elems, vec<int>& idx, int& cnt, int e){
            int i = idx[e];
            elems[i] = elems[cnt - 1];
            idx[elems[i]] = i;
            cnt --;
        }
        // current cost of the model
        Int model_scost = 0, model_hcost = 0;
        vec<bool>model;

        // cost of the best found solution
        Int best_found = INT32_MAX;

        // gaining score of variable when valued 
        // SAtLike will use sscore for total score
        vec<int> hscore, sscore;

        // literals which satisfy the clause
        vec<int> sat_cnt;
        // the last found satisfying lit stored as var
        vec<Var> last_sat;

        // unsatisfied clauses
        vec<int> unsat_hards, unsat_softs, unsat_idx;
        int cnt_unsat_hards = 0, cnt_unsat_softs = 0;

        // satisfied clauses for Satlike
        vec<int> sat_clauses; // index together with unsat clauses = unsat_idx
        int cnt_sat_clauses = 0;

        // satisfied hard clauses with weight > 1
        vec<int> sat_hard_bigs, sat_hard_bigs_idx;
        int cnt_sat_hard_bigs = 0;

        // variables with positive score on hard clauses
        // or with neutral score on hard clauses and positive score on soft clauses
        // Satlike uses hplus_scores as plus scores
        vec<int> hplus_scores, hzero_scores, scores_idx;
        int cnt_hplus_scores = 0, cnt_hzero_scores = 0;   

        vec<int> flip_time;

        vec<int> best_selected, selected_count;

        void initialize_metrics(bool is_satlike){
            model.growTo(V, 0);

            sscore.growTo(V, 0);
            
            sat_cnt.growTo(A, 0);
            last_sat.growTo(A);

            unsat_hards.growTo(H);
            unsat_softs.growTo(A-H);
            unsat_idx.growTo(A);

            hplus_scores.growTo(V);
            scores_idx.growTo(V);

            if(is_satlike){
              sat_clauses.growTo(A);

              flip_time.growTo(V, 0);

              best_selected.growTo(A-H);
              selected_count.growTo(A, 0);
            } else {
              hscore.growTo(V, 0);
              hzero_scores.growTo(V);
  
              sat_hard_bigs.growTo(H);
              sat_hard_bigs_idx.growTo(H);
            }
        }
        bool is_the_best(){
            if(model_hcost > 0) return false;
            if(model_scost < best_found){
                best_found = model_scost;
                return true;
            }
            return false;
        }
        void add_unsat(int c, int w){
            if(w >= 0) {
                increasePointerList(unsat_softs, unsat_idx, cnt_unsat_softs, c);
                model_scost += w;
            } else {
                increasePointerList(unsat_hards, unsat_idx, cnt_unsat_hards, c);
                model_hcost -= w;
            }
        }
        void subtract_unsat(int c, int w){
            if(w >= 0) {
                decreasePointerList(unsat_softs, unsat_idx, cnt_unsat_softs, c);
                model_scost -= w;
            } else {
                decreasePointerList(unsat_hards, unsat_idx, cnt_unsat_hards, c);
                model_hcost += w;
            }
        }
        void update_score(bool s, Var q, int w){
            if(s) sscore[q] += w;
            else hscore[q] += w;
        }
};
#endif