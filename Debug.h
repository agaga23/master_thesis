/*****************************************************************************************[Debug.h]
Copyright (c) 2005-2010, Niklas Een, Niklas Sorensson

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

#ifndef Debug_h
#define Debug_h

#include "minisat/core/SolverTypes.h"
#include "MsSolver.h"
#include "FEnv.h"


//=================================================================================================


extern vec<cchar*>* debug_names;

void dump(long num);
void dump(Int num);
void dump(Lit p);
void dump(Formula f);
void dump(const vec<Lit>& ps);
void dump(const Minisat::vec<Lit>& ps);
void dump(const vec<Lit>& ps, const vec<Int>& Cs);
void dump(const vec<Lit>& ps, const vec<Int>& Cs, const vec<int>& assigns);
void dump(const vec<Formula>& ps, const vec<Int>& Cs);
void dump(const Linear& pb, const vec<int>& assigns);
void dump(const Linear& pb);
macro void dump(Linear* pb) { dump(*pb); }


//=================================================================================================
#endif
