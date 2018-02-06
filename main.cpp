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
tuple<HaltFlag,Model,vector<char>> unit_propagation(Formula f, Model m, vector<char> undefs) {
	// Preprocess
	#ifdef TRACING
	fprintf(stderr, "  Prep: "); for (auto& i: m) fprintf(stderr, "%d%s ", i.first, i.second ? "" : "d"); fprintf(stderr, "\n");
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
		return make_tuple(HaltFlag::empty_formula, m, undefs);
	}
	// Check if empty clauses, if yes abort unit propagation
	if (find_if(f.begin(), f.end(), [](auto x){return x.empty();}) != f.end()) {
		return make_tuple(HaltFlag::empty_clause, m, undefs);
	}

	// Propagate
	while (true) {
		#ifdef TRACING
		fprintf(stderr, "  Prop: "); for (auto& i: m) fprintf(stderr, "%d%s ", i.first, i.second ? "" : "d"); fprintf(stderr, "\n");
		#endif

		const auto& unit = find_if(f.begin(), f.end(), [](auto x){return x.size() == 1;});  // Hot-spot
		if (unit == f.end()) {
			return make_tuple(HaltFlag::ok, m, undefs);
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
			undefs[abs(u)-1] = false;

			// Check if formula empty, if yes abort unit propagation
			if (f.empty()) {
				return make_tuple(HaltFlag::empty_formula, m, undefs);
			}
			// Check if empty clauses, if yes abort unit propagation
			if (find_if(f.begin(), f.end(), [](auto x){return x.empty();}) != f.end()) {
				return make_tuple(HaltFlag::empty_clause, m, undefs);
			}
		}
	}
}

pair<Model,vector<char>> backtrack(Model m, vector<char> undefs) {
	#ifdef TRACING
	fprintf(stderr, "  Backtracking, before: "); for (auto& i: m) fprintf(stderr, "%d%s ", i.first, i.second ? "" : "d"); fprintf(stderr, "\n");
	#endif
	while (!m.empty()) {
		auto x = m.back();
		if (x.second == false) {
			#ifdef TRACING
			fprintf(stderr, "  Backtracked, now: "); for (auto& i: m) fprintf(stderr, "%d%s ", i.first, i.second ? "" : "d"); fprintf(stderr, "\n");
			#endif
			return make_pair(m, undefs);
		}
		#ifdef TRACING
		fprintf(stderr, "  Popped %d%s\n", x.first, x.second ? "" : "d");
		#endif
		m.pop_back();
		undefs[abs(x.first)-1] = true;
	}
	#ifdef TRACING
	fprintf(stderr, "  Empty\n");
	#endif
	return make_pair(m, undefs);
}

pair<Formula,int> pureLitElim(Formula f, int nvars) {
	vector<Ident> pures;
	for (Ident i=1; i<=nvars; i++) {
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

	// vector<bool> undefs(nvars);
	vector<char> undefs(nvars);
	fill(undefs.begin(), undefs.end(), true);

	// While empty clauses
	while (true) {
		#ifdef TRACING
		for (auto& i: m) fprintf(stderr, "%d%s ", i.first, i.second ? "" : "d"); fprintf(stderr, "\n");
		for (Ident i=1; i<=nvars; i++) fprintf(stderr, "%d:%d ", i, undefs[i-1]); fprintf(stderr, "\n");
		#endif

		// Eagerly apply unit propagation
		HaltFlag flag;
		tie(flag, m, undefs) = unit_propagation(f, m, undefs);

		// If there is an empty clause
		if (flag == HaltFlag::empty_clause) {
			#ifdef TRACING
			fprintf(stderr, "  Found empty clause\n");
			#endif

			// Backtrack
			tie(m,undefs) = backtrack(m,undefs);
			// If impossible to backtrack anymore, conclude unsatisfiable
			if (m.empty()) {
				return false;
			}
			// Otherwise store latest decision, and attempt to backjump
			auto x = m.back();
			m.pop_back();
			#ifdef TRACING
			fprintf(stderr, "  Found decision literal %d%s\n", x.first, x.second ? "" : "d");
			#endif

			// Backjumping
			while (true) {
				Model m_ ;
				vector<char> undefs_;
				tie(m_, undefs_) = backtrack(m, undefs);
				// No more backtracking possible
				if (m_.empty()) {
					break;
				}
				// If another decision was found, check if taking it off (and putting in x) still yields a conflict
				auto y = m_.back();
				m_.pop_back();
				#ifdef TRACING
				fprintf(stderr, "  Attempting backjump to %d%s (\n", y.first, y.second ? "" : "d");
				#endif
				m_.push_back(x);
				tie(flag, ignore, ignore) = unit_propagation(f, m_, undefs);
				// If not then we can't backjump anymore
				if (flag != HaltFlag::empty_clause) {
					#ifdef TRACING
					fprintf(stderr, "  ) No conflict.\n");
					#endif
					// m.pop_back();
					// m.push_back(y);
					break;
				} 
				// If yes then this backjump was successful: update the model and try backjumping again
				else {
					#ifdef TRACING
					fprintf(stderr, "  ) Conflict.\n");
					#endif
					m_.pop_back();
					m = m_;
					undefs = undefs_;
					undefs[abs(y.first)-1] = true;
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
			fprintf(stderr, "  Pushed %d%s\n", x.first, x.second ? "" : "d");
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
			/*auto ptr = undefs.end();
			for (auto& i: m) {
				ptr = remove(undefs.begin(), ptr, abs(i.first));
			}
			undefs.erase(ptr, undefs.end());*/
			Ident choice;
			int freq = 0;
			// for (auto i: undefs) {
			for (Ident i=-nvars; i<=nvars; i++) {
				if (i==0 || undefs[abs(i)-1]==false) continue;
				// Count occurences
				int fr = count_if(f.begin(), f.end(), [i](Clause x){return find(x.begin(), x.end(), i) != x.end();});
				#ifdef TRACING
				fprintf(stderr, "  num %d freq %d\n", i, fr);
				#endif
				if (fr > freq) {
					choice = i;
					freq = fr;
				}
			}
			m.push_back(make_pair(choice, false));
			undefs[abs(choice)-1] = false;
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
	Model m(0);
	m.reserve(nclauses);

	#ifdef TRACING
	print_formula(f, stderr);
	#endif

	bool result = dpll(f, m, nvars);

	printf("%s", result ? "SATISFIABLE\n" : "UNSATISFIABLE\n");

	return 0;
}