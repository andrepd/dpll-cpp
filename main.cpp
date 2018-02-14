#include <cstdio>
#include <vector>
#include <algorithm>
#include <tuple>
#include <cassert>
#include <utility>
#include <numeric>

using namespace std;

using Ident = int;
enum class Assignment : char { Unset=-1, False=0, True=1 };
using Clause = vector<Ident>;
using Formula = vector<Clause>;
// enum class DPLLFlag : bool { Guessed=false, Derived=true };
using DerivedLit = pair<Ident,bool>;

// using Model = vector<DerivedLit>;
// Wrapper around a vector that does *not* destruct objects after removing them, but merely moves the (pseudo-).end() iterator back. This allows for cheap backtracking and cheap restoring the state to before an undesired backtrack (all you need to do is store the head position, backtrack, and if you wish to undo just restore the head from the save)
struct Model {
	vector<DerivedLit> m;
	vector<DerivedLit>::iterator head;

	Model(const Formula& f) {
		m = vector<DerivedLit>(0);
		m.reserve(f.size());
		head = m.begin();
	}

	void push(const DerivedLit& x) {
		if (head == m.end()) {
			m.push_back(x);	
			head = m.end();
		} else {
			*head = x;
			head++;
		}
	}

	void pop() {
		head--;
	}

	vector<DerivedLit>::iterator begin() { return m.begin(); }
	vector<DerivedLit>::iterator end()   { return head; }
	bool empty() { return begin() == end(); }
	DerivedLit& back() { return *(head-1); }
	auto size() { return distance(begin(), end()); }
};

int sign(int x) { return (x>0) - (x<0); }

struct WatchList {
	vector<vector<size_t>> _lit2clause;
	vector<array<Ident,2>> _clause2lit;
	vector<Assignment> _assignments;

	vector<size_t>& lit2clause(const Ident n) { return _lit2clause[n+nvars]; }
	array<Ident,2>& clause2lit(const size_t n) { return _clause2lit[n]; }
	Assignment& assignments(const Ident n) { return _assignments[abs(n)-1]; }

	void set_assignment(const Ident lit) {
		const auto idx = abs(lit)-1;
		const auto sgn = sign(lit);
		_assignments[idx] = sgn==1 ? Assignment::True : Assignment::False;
	}

	Assignment get_assignment(const Ident lit) {
		const auto idx = abs(lit)-1;
		const auto sgn = sign(lit);
		const auto a = _assignments[idx];
		if (a == Assignment::Unset) {
			return a;
		} else if (sgn==1) {
			return a;
		} else {
			return a==Assignment::True ? Assignment::False : Assignment::True;
		}
	}

	WatchList(int nvars_, const Formula& f) {
		_lit2clause = vector<vector<size_t>>(2*nvars_+1);
		_clause2lit	= vector<array<Ident,2>>(f.size());
		_assignments = vector<Assignment>(nvars_, Assignment::Unset);
		nvars = nvars_;

		for (int i=0; i<f.size(); i++) {
			lit2clause(f[i][0]).push_back(i);
			lit2clause(f[i][1]).push_back(i);

			_clause2lit[i][0] = f[i][0];
			_clause2lit[i][1] = f[i][1];
		}
	}

	int nvars;
};

void print_formula(Formula f, FILE* file=stdout) {
	fprintf(file, "(\n");
	for (auto i: f) {
		for (auto j: i) {
			fprintf(file, "%d,", j);
		}
		fprintf(file, ";\n");
	}	
	fprintf(file, ")\n");
}

enum class HaltFlag : bool { ok, empty_clause };

DerivedLit negate(DerivedLit x) {
	return make_pair(-x.first, !x.second);
}

// Helper functions
template<typename InputIt, typename T>
bool exists(InputIt first, InputIt last, const T& value) {
	return find(first, last,  value) != last;
}

template<typename InputIt, typename UnaryPredicate>
bool exists_if(InputIt first, InputIt last, UnaryPredicate pred) {
	return find_if(first, last,  pred) != last;
}

template<typename T>
vector<size_t> sorted_vector_indices(const vector<T>& v) {
	vector<size_t> ret(v.size());
	iota(ret.begin(), ret.end(), 0);
	sort(ret.begin(), ret.end(), [&](auto x, auto y){return v[x] > v[y];});	
	return ret;
}

template<bool update_model>
HaltFlag unit_propagation(const Formula& f, Model& m, WatchList& watch, const Ident lit) {
	#ifdef TRACING
	fprintf(stderr, "  Propagating %d\n", lit);
	// fprintf(stderr, "  Watched literals:\n"); for (int i=0; i<watch._clause2lit.size(); i++) fprintf(stderr, "    %d: %d %d\n", i, watch._clause2lit[i][0], watch._clause2lit[i][1]);
	#endif

	auto& clauses = watch.lit2clause(-lit);
	for (int i=0; i<clauses.size(); i++) {
		auto& c = clauses[i];
		#ifdef TRACING
		fprintf(stderr, "  Clause #%d (%d)\n", i, c);
		#endif
		Ident& one = watch.clause2lit(c)[0];
		Ident& two = watch.clause2lit(c)[1];
		Ident& these = one==-lit ? one : two;
		Ident& other = one==-lit ? two : one;

		#ifdef TRACING
		fprintf(stderr, "  This: %d:%d Other: %d:%d\n", these, static_cast<int>(watch.get_assignment(these)), other, static_cast<int>(watch.get_assignment(other)));
		#endif

		// If the other is true, do nothing
		if (watch.get_assignment(other) == Assignment::True) {
			;
		} 
		// Else, if there is another unwatched literal not marked false, make it the new watched literal
		else if (
				const auto ptr_lit_ = find_if(f[c].begin(), f[c].end(), [&](auto x) {
					return x != one && x != two && watch.get_assignment(x) != Assignment::False;
				});
				ptr_lit_ != f[c].end()
				) {
			const Ident lit_ = *ptr_lit_;

			#ifdef TRACING
			fprintf(stderr, "  Deleting and putting on %d\n", lit_);
			#endif
			// Remove c from the watchlist of -lit and put it onto the watchlist of lit_
			watch.lit2clause(lit_).push_back(c);
			clauses.erase(clauses.begin()+i);
			i--;
			// Put lit_ instead of -lit on the watchlist of c
			these = lit_;
			#ifdef TRACING
			// fprintf(stderr, "  Now watched: "); for (int i=-watch.nvars; i<=watch.nvars; i++) {if (i==0) continue; fprintf(stderr, "%d: ", i); for (auto j: watch.lit2clause(i)) fprintf(stderr, "%d ", j); fprintf(stderr, "\b, ");} fprintf(stderr, "\n");
			#endif			
		}
		// Else (if there are no more nonfalse literals in the clause), if the other watched literal is unset then it is a unit clause: propagate
		else if (watch.get_assignment(other) == Assignment::Unset) {
			#ifdef TRACING
			fprintf(stderr, "  Entering..\n");
			#endif			
			if constexpr (update_model) {
				m.push(make_pair(other, true));
			}
			watch.set_assignment(other);
			const HaltFlag flag = unit_propagation<update_model>(f, m, watch, other);
			// If a conflict is found immediately end unit propagation and process conflict
			if (flag != HaltFlag::ok) {
				#ifdef TRACING
				fprintf(stderr, "  Exiting [sub-conflict]..\n");
				#endif			
				return flag;
			}
		} 
		// Else (if there are no more nonfalse literals in the clause and the other watched literal is set) then we have found a conflict
		else {
			#ifdef TRACING
			fprintf(stderr, "  Exiting [conflict]..\n");
			#endif			
			return HaltFlag::empty_clause;
		}
		#ifdef TRACING
		// fprintf(stderr, "  New watched literals:\n"); for (int i=0; i<watch._clause2lit.size(); i++) fprintf(stderr, "    %d: %d %d\n", i, watch._clause2lit[i][0], watch._clause2lit[i][1]);
		#endif
	}
	#ifdef TRACING
	fprintf(stderr, "  Exiting [ok]..\n");
	#endif			
	return HaltFlag::ok;
}

void backtrack(Model& m, WatchList& watch) {
	#ifdef TRACING
	fprintf(stderr, "  Backtracking, before: "); for (auto& i: m) fprintf(stderr, "%d%s ", i.first, i.second ? "" : "d"); fprintf(stderr, "\n");
	#endif
	while (!m.empty()) {
		const auto& x = m.back();
		if (x.second == false) {
			#ifdef TRACING
			fprintf(stderr, "  Backtracked, now: "); for (auto& i: m) fprintf(stderr, "%d%s ", i.first, i.second ? "" : "d"); fprintf(stderr, "\n");
			#endif
			return;
		}
		#ifdef TRACING
		fprintf(stderr, "  Popped %d%s\n", x.first, x.second ? "" : "d");
		#endif
		m.pop();
		watch.assignments(x.first) = Assignment::Unset;
	}
	#ifdef TRACING
	fprintf(stderr, "  Empty\n");
	#endif
	return;
}

Formula pureLitElim(Formula f, int nvars) {
	vector<Ident> pures;
	for (Ident i=1; i<=nvars; i++) {
		if ((exists_if(f.begin(), f.end(), [i](Clause x){return exists(x.begin(), x.end(),  i);}))
		 != (exists_if(f.begin(), f.end(), [i](Clause x){return exists(x.begin(), x.end(), -i);}))) {
			#ifdef TRACING
			fprintf(stderr, "Pure lit: %d\n", i);
			#endif
			pures.push_back(i);
		}
	}

	for (auto i: pures) {
		// Remove formulas containing i or -i
		f.erase(remove_if(f.begin(), f.end(), [i](auto x){return (exists(x.begin(), x.end(), i)) || (exists(x.begin(), x.end(), -i));}), f.end());
	}

	return f;
}

bool dpll(Formula f, int nvars) {	
	// Remove duplicate terms in clauses and duplicate clauses
	for (auto& i: f) {
		sort(i.begin(), i.end());
		i.erase(unique(i.begin(), i.end()), i.end());
	}
	sort(f.begin(), f.end());
	f.erase(unique(f.begin(), f.end()), f.end());

	// Pure literal elimination
	f = pureLitElim(f, nvars);

	#ifdef TRACING
	fprintf(stderr, "After pureLitElim:\n");
	print_formula(f, stderr);
	#endif

	// Check: if -n and n in any clause, remove the clause
	for (int i=0; i<f.size(); i++) {
		auto& c = f[i];
		for (int n=1; n<=nvars; n++) {
			if (exists(c.begin(), c.end(), n) && exists(c.begin(), c.end(), -n)) {
				#ifdef TRACING
				fprintf(stderr, "Erasing clause %d\n", i);
				#endif
				f.erase(f.begin()+i);
				i--;
				break;
			}
		}
	}

	Model m(f);

	// Add missing variables (removed by the procedures above) to trail as deduced
	{
		vector<char> missing(nvars, false);
		for (auto i: f) {
			for (auto j: i) {
				missing[abs(j)-1] = true;
			}
		}
		for (int i=0; i<nvars; i++) {
			if (!missing[i]) {
				#ifdef TRACING
				fprintf(stderr, "Missing %d\n", i+1);
				#endif
				m.push(make_pair(i+1, true));
			}
		}
	}

	#ifdef TRACING
	fprintf(stderr, "After tautology removal:\n")
	print_formula(f, stderr);
	#endif

	// Watched literals
	WatchList watch(nvars, f);

	// Make 0-level unit propagation
	while (true) {
		#ifdef TRACING
		fprintf(stderr, "  Prop: "); for (auto& i: m) fprintf(stderr, "%d%s ", i.first, i.second ? "" : "d"); fprintf(stderr, "\n");
		#endif

		const auto& unit = find_if(f.begin(), f.end(), [](auto x){return x.size() == 1;});
		if (unit == f.end()) {
			break;
		} else {
			const auto u = (*unit)[0];
			const auto u_ = -1*u;
			#ifdef TRACING
			fprintf(stderr, "  Found unit %d\n", u);
			#endif
			f.erase(remove_if(f.begin(), f.end(), [u](auto x){return exists(x.begin(), x.end(), u);}), f.end());
			// transform(f.begin(), f.end(), f.begin(), [u_](auto x){return remove()})
			for (auto& i: f)
				i.erase(remove(i.begin(), i.end(), u_), i.end());

			#ifdef TRACING
			print_formula(f ,stderr);
			#endif

			// Update model
			m.push(make_pair(u, true));
			watch.set_assignment(u);  ////////

			// Check if formula empty, if yes abort unit propagation
			if (f.empty()) {
				return true;
			}
			// Check if empty clauses, if yes abort unit propagation
			if (exists_if(f.begin(), f.end(), [](auto x){return x.empty();})) {
				return false;
			}
		}
	}

	#ifdef TRACING
	fprintf(stderr, "After initial propagation:\n")
	print_formula(f, stderr);
	#endif

	// Make first decision
	vector<int> freqs(nvars, 0);
	for (auto& i: f) {
		for (auto& j: i) {
			freqs[abs(j)-1]++;
		}
	}
	#ifdef TRACING
	fprintf(stderr, "  Freqs: "); for (int i=0; i<nvars; i++) fprintf(stderr, "%d:%d ", i+1, freqs[i]); fprintf(stderr, "\n");
	#endif
	vector<size_t> ifreqs = sorted_vector_indices(freqs);
	#ifdef TRACING
	fprintf(stderr, "  iFreqs: "); for (int i=0; i<nvars; i++) fprintf(stderr, "%d ", ifreqs[i]); fprintf(stderr, "\n");
	#endif

	const Ident choice = ifreqs.front() + 1;
	m.push(make_pair(choice, false));
	watch.set_assignment(choice);

	// Main loop
	while (true) {
		#ifdef TRACING
		for (auto& i: m) fprintf(stderr, "%d%s ", i.first, i.second ? "" : "d"); fprintf(stderr, "\n");
		// for (Ident i=1; i<=nvars; i++) fprintf(stderr, "%d:%d ", i, undefs[i-1]); fprintf(stderr, "\n");
		#endif
		#ifdef TRACING
		fprintf(stderr, "  Watched: "); for (int i=-nvars; i<=nvars; i++) {if (i==0) continue; fprintf(stderr, "%d: ", i); for (auto j: watch.lit2clause(i)) fprintf(stderr, "%d ", j); fprintf(stderr, "\b, ");} fprintf(stderr, "\n");
		fprintf(stderr, "  Assignments: "); for (int i=1; i<=nvars; i++) fprintf(stderr, "%d:%d ", i, static_cast<int>(watch.assignments(i))); fprintf(stderr, "\n");
		#endif

		// Eagerly apply unit propagation
		HaltFlag flag;
		flag = unit_propagation<true>(f, m, watch, m.back().first);

		// If all variables assigned, then we have a model: formula is satisfiable
		if (flag == HaltFlag::ok && m.size() == nvars) {
			for (auto i: m) fprintf(stderr, "%d ", i.first); fprintf(stderr, "\n");
			return true;
		}

		// If there is an empty clause
		else if (flag == HaltFlag::empty_clause) {
			#ifdef TRACING
			fprintf(stderr, "  Found empty clause\n");
			#endif

			// Backtrack
			backtrack(m, watch);
			// If impossible to backtrack anymore, conclude unsatisfiable
			if (m.empty()) {
				return false;
			}
			// Otherwise store latest decision, and attempt to backjump
			auto x = m.back();
			m.pop();
			#ifdef TRACING
			fprintf(stderr, "  Found decision literal %d%s\n", x.first, x.second ? "" : "d");
			#endif

			// Backjumping
			while (true) {
				// Save model state;
				auto model_head_save = m.head;
				auto assignments_save = watch._assignments;
				backtrack(m, watch);
				// No more backtracking possible
				if (m.empty()) {
					// Restore
					m.head = model_head_save;
					watch._assignments = assignments_save;
					break;
				}
				// If another decision was found, check if taking it off (and putting in x) still yields a conflict
				auto y = m.back();
				m.back() = x;
				watch.assignments(y.first) = Assignment::Unset;
				#ifdef TRACING
				fprintf(stderr, "  Attempting backjump to %d%s (\n", y.first, y.second ? "" : "d");
				#endif
				// watch.set_assignment(x.first);
				#ifdef TRACING
				fprintf(stderr, "  Now trail looks like: "); for (auto& i: m) fprintf(stderr, "%d%s ", i.first, i.second ? "" : "d"); fprintf(stderr, "\n");
				#endif
				auto assignments_save_ = watch._assignments;
				flag = unit_propagation<false>(f, m, watch, m.back().first);
				watch._assignments = assignments_save_;
				// If not then we can't backjump anymore
				if (flag != HaltFlag::empty_clause) {
					#ifdef TRACING
					fprintf(stderr, "  ) No conflict.\n");
					#endif
					// Restore
					m.back() = y;
					m.head = model_head_save;
					watch._assignments = assignments_save;
					// m.push(x);
					break;
				} 
				// If yes then this backjump was successful: update the model and try backjumping again
				else {
					#ifdef TRACING
					fprintf(stderr, "  ) Conflict.\n");
					#endif
					m.pop();
				}
			}

			// Build the conflict clause
			Clause conflict;
			// copy_if(m.begin(), m.end(), back_inserter(conflict), [](DerivedLit x){return x.second == false;});
			// transform(conflict.begin(), conflict.end(), [](Ident x){return -x;});
			for (auto i: m) {
				if (i.second == false) {
					conflict.push_back(-i.first);
				}
			}
			conflict.push_back(-x.first);
			if (conflict.size() != 1 && false) {
				// Add the conflict clause watched literals
				watch.lit2clause(conflict[0]).push_back(f.size());
				watch.lit2clause(conflict[1]).push_back(f.size());
				watch._clause2lit.push_back({conflict[0],conflict[1]});
				f.push_back(conflict);
			}

			// Append the conflict clause and push the last decision literal
			x.first *= -1;
			x.second = true;
			#ifdef TRACING
			fprintf(stderr, "  Pushed %d%s\n", x.first, x.second ? "" : "d");
			fprintf(stderr, "  Conflict: "); for (auto i: conflict) fprintf(stderr, "%d ", i); fprintf(stderr, "\n");
			#endif
			m.push(x);
			watch.set_assignment(x.first);
		}

		// If not, then we have to make a decision
		else {
			#ifdef TRACING
			fprintf(stderr, "  Case split\n");
			#endif
			for (auto i: ifreqs) {
				#ifdef TRACING
				// fprintf(stderr, )
				#endif
				if (watch._assignments[i] == Assignment::Unset) {
					const Ident choice = i+1;
					m.push(make_pair(choice, false));
					watch.set_assignment(choice);
					break;
				}
			}
		}
	}
}

int main(int argc, char const *argv[])
{
	int nvars, nclauses;
	scanf("%*s %*s %d %d", &nvars, &nclauses);
	#ifdef TRACING
	fprintf(stderr, "%d %d\n", nvars, nclauses);
	#endif
	Formula f(nclauses);
	for (int i=0; i<nclauses; i++) {
		while (true) {
			int n;
			scanf("%d", &n);
			if (n == 0) break;
			f[i].push_back(n);
		}
	}

	#ifdef TRACING
	print_formula(f, stderr);
	#endif

	bool result = dpll(f, nvars);

	printf(result ? "SATISFIABLE\n" : "UNSATISFIABLE\n");

	return 0;
}
