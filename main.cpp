#include <cstdio>
#include <vector>
#include <algorithm>
#include <tuple>

using namespace std;

using Ident = int;
using Clause = vector<Ident>;
using Formula = vector<Clause>;
enum class DPLLFlag : bool { Guessed=false, Derived=true };
using DerivedLit = pair<Ident,bool>;
using Model = vector<DerivedLit>;

#ifdef NOFORM_TRACING
void print_formula(Formula f, FILE* file=stdout) {
	return;
}
#else
void print_formula(Formula f, FILE* file=stdout) {
	fprintf(file, "(\n");
	for (auto i: f) {
		for (auto j: i) {
			// #ifdef TRACING
			fprintf(file, "%d,", j);
			// #endif
		}
		// #ifdef TRACING
		fprintf(file, ";\n");
		// #endif
	}	
	fprintf(file, ")\n");
}
#endif

enum class HaltFlag { ok, empty_clause, empty_formula };

// DerivedLit negate(DerivedLit x) {
// 	return make_pair(-x.first, )
// }

// 0 OK, 1 empty clause, 2 empty formula
pair<HaltFlag,Model> unit_propagation(Formula f, Model m) {
	// Preprocess
	#ifdef TRACING
	fprintf(stderr, "  Prep: "); for (auto& i: m) fprintf(stderr, "%d/%d ", i.first, i.second); fprintf(stderr, "\n");
	#endif
	for (auto& i: m) {	
		const auto& u = i.first;
		const auto  u_ = -1*u;
		f.erase(remove_if(f.begin(), f.end(), [u](auto x){return find(x.begin(), x.end(), u) != x.end();}), f.end());
		for (auto& i: f) {
			i.erase(remove(i.begin(), i.end(), u_), i.end());
		}
	}
	#ifdef TRACING
	print_formula(f ,stderr);
	#endif
	// Check if formula empty, if yes abort unit propagation
	if (f.empty()) {
		return make_pair(HaltFlag::empty_formula, m);
	}
	// Check if empty clauses, if yes abort unit propagation
	if (find_if(f.begin(), f.end(), [](auto x){return x.empty();}) != f.end()) {
		return make_pair(HaltFlag::empty_clause, m);
	}

	// Propagate
	while (true) {
		#ifdef TRACING
		fprintf(stderr, "  Prop: "); for (auto& i: m) fprintf(stderr, "%d/%d ", i.first, i.second); fprintf(stderr, "\n");
		#endif

		const auto& unit = find_if(f.begin(), f.end(), [](auto x){return x.size() == 1;});  // Hot-spot
		if (unit == f.end()) {
			return make_pair(HaltFlag::ok, m);
		} else {
			const auto u = (*unit)[0];
			const auto u_ = -1*u;
			#ifdef TRACING
			fprintf(stderr, "  Found unit %d\n", u);
			#endif
			// f.erase(remove_if(f.begin(), f.end(), [u](auto x){fprintf(stderr, "  > %d\n", find(x.begin(), x.end(), u) != x.end()); return find(x.begin(), x.end(), u) != x.end();}));
			f.erase(remove_if(f.begin(), f.end(), [u](auto x){return find(x.begin(), x.end(), u) != x.end();}), f.end());
			// transform(f.begin(), f.end(), f.begin(), [u_](auto x){return remove()})
			for (auto& i: f)
				i.erase(remove(i.begin(), i.end(), u_), i.end());

			#ifdef TRACING
			print_formula(f ,stderr);
			#endif

			// Update model
			m.push_back(make_pair(u, true));

			// Check if formula empty, if yes abort unit propagation
			if (f.empty()) {
				return make_pair(HaltFlag::empty_formula, m);
			}
			// Check if empty clauses, if yes abort unit propagation
			if (find_if(f.begin(), f.end(), [](auto x){return x.empty();}) != f.end()) {
				return make_pair(HaltFlag::empty_clause, m);
			}
		}
	}
}

Model backtrack(Model m) {
	#ifdef TRACING
	fprintf(stderr, "  Backtracking, before: "); for (auto& i: m) fprintf(stderr, "%d/%d ", i.first, i.second); fprintf(stderr, "\n");
	#endif
	while (!m.empty()) {
		auto x = m.back();
		if (x.second == false) {
			#ifdef TRACING
			fprintf(stderr, "  Backtracked, now: "); for (auto& i: m) fprintf(stderr, "%d/%d ", i.first, i.second); fprintf(stderr, "\n");
			#endif
			return m;
		}
		#ifdef TRACING
		fprintf(stderr, "  Popped %d/%d\n", x.first, x.second);
		#endif
		m.pop_back();
	}
	#ifdef TRACING
	fprintf(stderr, "  Empty\n");
	#endif
	return m;
}

Model backjump(Model m) {
	while (!m.empty()) {
		m = backtrack(m);
	}
	return m;
}

pair<Formula,int> pureLitElim(Formula f, int nvars) {
	vector<Ident> pures;
	for (int i=1; i<=nvars; i++) {
		if ((find_if(f.begin(), f.end(), [i](Clause x){return find(x.begin(), x.end(),  i) != x.end();}) != f.end())
		 != (find_if(f.begin(), f.end(), [i](Clause x){return find(x.begin(), x.end(), -i) != x.end();}) != f.end())) {
			#ifdef TRACING
			fprintf(stderr, "Pure lit: %d\n", i);
			#endif
			pures.push_back(i);
		}
	}

	for (auto i: pures) {
		// Delete i
		f.erase(remove_if(f.begin(), f.end(), [i](auto x){return (find(x.begin(), x.end(), i) != x.end()) || (find(x.begin(), x.end(), -i) != x.end());}), f.end());
		// Replace instances of nvars with i
		for (auto& j: f) {
			replace(j.begin(), j.end(),  nvars,  i);
			replace(j.begin(), j.end(), -nvars, -i);
		}
		// Decrement nvars
		nvars--;
	}

	return make_pair(f, nvars);
}

bool dpll(Formula f, Model m, int nvars) {
	// Remove duplicate terms in clauses and duplicate clauses
	for (auto& i: f) {
		sort(i.begin(), i.end());
		i.erase(unique(i.begin(), i.end()), i.end());
	}
	sort(f.begin(), f.end());
	f.erase(unique(f.begin(), f.end()), f.end());

	// Pure literal elimination
	tie(f, nvars) = pureLitElim(f, nvars);

	// While empty clauses
	while (true) {
		#ifdef TRACING
		for (auto& i: m) fprintf(stderr, "%d/%d ", i.first, i.second); fprintf(stderr, "\n");
		#endif

		// Eagerly apply unit propagation
		HaltFlag flag;
		tie(flag, m) = unit_propagation(f, m);
		// If there is an empty clause
		if (flag == HaltFlag::empty_clause) {
			#ifdef TRACING
			fprintf(stderr, "  Found empty clause\n");
			#endif

			// Backtrack
			m = backtrack(m);
			// If impossible to backtrack anymore, conclude unsatisfiable
			if (m.empty()) {
				return false;
			}
			// Otherwise store latest decision, and attempt to backjump
			auto x = m.back();
			m.pop_back();
			#ifdef TRACING
			fprintf(stderr, "  Found decision literal %d/%d\n", x.first, x.second);
			#endif

			/*x.first *= -1;
			x.second = true;
			#ifdef TRACING
			fprintf(stderr, "  Pushed %d/%d\n", x.first, x.second);
			#endif
			m.push_back(x);*/

			// Backjumping
			while (true) {
				Model m_ = backtrack(m);
				// No more backtracking possible
				if (m_.empty()) {
					break;
				}
				// If another decision was found, check if taking it off (and putting in x) still yields a conflict
				auto y = m_.back();
				m_.pop_back();
				#ifdef TRACING
				fprintf(stderr, "  Attempting backjump to %d/%d (\n", y.first, y.second);
				#endif
				m_.push_back(x);
				tie(flag, ignore) = unit_propagation(f, m_);
				// If not then we can't backjump anymore
				if (flag != HaltFlag::empty_clause) {
					#ifdef TRACING
					fprintf(stderr, "  ) No conflict.\n");
					#endif
					// m.pop_back();
					// m.push_back(y);
					break;
				} 
				// If yes then we can assert this backjump was successful, update the model, and try further
				else {
					#ifdef TRACING
					fprintf(stderr, "  ) Conflict.\n");
					#endif
					m_.pop_back();
					m = m_;
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

			// Append the conflict clause and push the last decision literal
			x.first *= -1;
			x.second = true;
			#ifdef TRACING
			fprintf(stderr, "  Pushed %d/%d\n", x.first, x.second);
			fprintf(stderr, "  Conflict: "); for (auto i: conflict) fprintf(stderr, "%d ", i); fprintf(stderr, "\n");
			#endif
			f.push_back(conflict);
			m.push_back(x);
		}
		// If not
		else {
			// If all assigned
			// if (m.size() == nvars) {
			if (flag == HaltFlag::empty_formula) {
				return true;
			}
			// Else case-split
			for (Ident i=1; i<=nvars; i++) {
				// Naive choice
				if (find_if(m.begin(), m.end(), [i](auto x){return x.first == i || x.first == -i;}) == m.end()) {
					#ifdef TRACING
					fprintf(stderr, "  Adding %d\n", i);
					#endif
					m.push_back(make_pair(i, false));
					break;
				}
			}
		}
	}
}

// Assumes comments are stripped out, for simplicity. Auxiliary script feeds input after `grep -v '^c'`
Formula read_formula(FILE*=stdin) {
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
	return f;	
}

int main(int argc, char const *argv[])
{
	f = read_formula();
	Model m();
	m.reserve(nclauses);

	#ifdef TRACING
	print_formula(f, stderr);
	#endif

	bool result = dpll(f, m, nvars);

	printf("%s", result ? "SATISFIABLE\n" : "UNSATISFIABLE\n");

	return 0;
}