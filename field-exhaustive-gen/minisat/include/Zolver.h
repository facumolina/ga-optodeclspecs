#ifndef RFM_Zolver_h
#define RFM_Zolver_h

//#include "minisat/mtl/Vec.h"
//#include "minisat/mtl/Heap.h"
//#include "minisat/mtl/Alg.h"
//#include "minisat/mtl/IntMap.h"
//#include "minisat/utils/Options.h"
//#include "minisat/core/SolverTypes.h"

#include <vector>
#include "minisat/core/Solver.h"
#include "minisat/core/SolverTypes.h"

using Minisat::mkLit;
using Minisat::lbool;

typedef Minisat::Var Var;


class Zolver : public Minisat::Solver {
 public:
    Zolver();
    ~Zolver();

	double getvaractivity(Var v) const { return activity[v]; }

	float getclauseactivity(unsigned long ith) {
		return ca[clauses[ith]].activity();
	}

	float getlearntactivity(unsigned long ith) {
		return ca[learnts[ith]].activity();
	}
	
	std::vector<int> getclause(unsigned long ith) const {
		const Minisat::Clause &c = ca[clauses[ith]];
		int n = c.size();
		std::vector<int> result(n);
		for(int i = 0; i < n; ++i) {
			const Minisat::Lit &x = c[i];
			result[i] = Minisat::sign(x) ? -(Minisat::var(x)+1) : (Minisat::var(x)+1);
		}
		return result;
	}
	
	bool issatisfiedclause(unsigned long ith) const {
		return satisfied(ca[clauses[ith]]);
	}
	
	std::vector<int> getclause_nofalselits(unsigned long ith) const {
		const Minisat::Clause &c = ca[clauses[ith]];
		std::vector<int> result;
		if(!satisfied(c)) {
			int n = c.size();
			for(int i = 0; i < n; ++i) {
				const Minisat::Lit &x = c[i];
				if(value(x) != l_False) {
					result.push_back(Minisat::sign(x) ? 
						-(Minisat::var(x)+1) :
						 (Minisat::var(x)+1) );
				}
			}
		}
		return result;
	}

	std::vector<int> getlearnt(unsigned long ith) const {
		const Minisat::Clause &c = ca[learnts[ith]];
		int n = c.size();
		std::vector<int> result(n);
		for(int i = 0; i < n; ++i) {
			const Minisat::Lit &x = c[i];
			result[i] = Minisat::sign(x) ? -(Minisat::var(x)+1) : (Minisat::var(x)+1);
		}
		return result;
	}

        // BEGIN NACHO
        void reset_max_learnts() {
                if (this->nLearnts() > (this->nClauses() * this->learntsize_factor)) 
                {
                        this->max_learnts = this->nLearnts();
                }
                else 
                {
                        this->max_learnts = this->nClauses() * this->learntsize_factor;
                }
        }

        void set_max_learnts(int limit)
        {
                if(limit >= 0)
                        this->max_learnts = limit; 
        }

        int get_max_learnts() { return this->max_learnts; }

        void set_current_restarts(int restarts)
        {
                if(restarts >= 0)
                        this->curr_restarts = restarts;
        }

        std::vector<int> get_learnt_facts()
        {
		std::vector<int> to;
                for(int i = 0; i < this->nVars(); i++)
                {
                        if(this->assigns[i] != l_Undef)
                        {
                                if((this->vardata[i].reason == Minisat::CRef_Undef) && (this->vardata[i].level == 0)) // It's a learnt fact!
                                {
                                        to.push_back((this->assigns[i] == l_True)?i+1:-1*(i+1));
                                }
                        }
                }
		return to;
        }

        int get_current_restarts() { return this->curr_restarts; }

        int getlearntlbd(int ith)
        {
        	return ca[learnts[ith]].lbd();
        }
        // END NACHO
};

#endif
