#include <cstdio>
#include <vector>
#include <algorithm>
#include <tuple>

using namespace std;

using Ident = int;
using Formula = vector<vector<Ident>>;
using DerivedLit = pair<Ident,bool>;
using Model = vector<DerivedLit>;

void print_formula(Formula f, FILE* file=stdout) {
	fprintf(file, "(\n");
	for (auto i: f) {
		for (auto j: i) {
			// #ifdef DEBUG_PRINTS
			fprintf(file, "%d,", j);
			// #endif
		}
		// #ifdef DEBUG_PRINTS
		fprintf(file, ";\n");
		// #endif
	}	
	fprintf(file, ")\n");
}

enum class HaltFlag { ok, empty_clause, empty_formula };

// 0 OK, 1 empty clause, 2 empty formula
pair<HaltFlag,Model> unit_propagation(Formula f, Model m) {
	// Preprocess
	#ifdef DEBUG_PRINTS
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
	#ifdef DEBUG_PRINTS
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
		#ifdef DEBUG_PRINTS
		fprintf(stderr, "  Prop: "); for (auto& i: m) fprintf(stderr, "%d/%d ", i.first, i.second); fprintf(stderr, "\n");
		#endif

		const auto& unit = find_if(f.begin(), f.end(), [](auto x){return x.size() == 1;});
		if (unit == f.end()) {
			return make_pair(HaltFlag::ok, m);
		} else {
			const auto u = (*unit)[0];
			const auto u_ = -1*u;
			#ifdef DEBUG_PRINTS
			fprintf(stderr, "  Found unit %d\n", u);
			#endif
			// f.erase(remove_if(f.begin(), f.end(), [u](auto x){fprintf(stderr, "  > %d\n", find(x.begin(), x.end(), u) != x.end()); return find(x.begin(), x.end(), u) != x.end();}));
			f.erase(remove_if(f.begin(), f.end(), [u](auto x){return find(x.begin(), x.end(), u) != x.end();}), f.end());
			// transform(f.begin(), f.end(), f.begin(), [u_](auto x){return remove()})
			for (auto& i: f)
				i.erase(remove(i.begin(), i.end(), u_), i.end());

			#ifdef DEBUG_PRINTS
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

bool dpll(Formula f, Model m, int nvars) {
	// Remove duplicate terms in clauses and duplicate clauses
	for (auto& i: f) {
		sort(i.begin(), i.end());
		i.erase(unique(i.begin(), i.end()), i.end());
	}
	sort(f.begin(), f.end());
	f.erase(unique(f.begin(), f.end()), f.end());

	// Pure literal elimination
	
	
	// While empty clauses
	while (true) {
		#ifdef DEBUG_PRINTS
		for (auto& i: m) fprintf(stderr, "%d/%d ", i.first, i.second); fprintf(stderr, "\n");
		#endif

		// Eagerly apply unit propagation
		HaltFlag flag;
		tie(flag, m) = unit_propagation(f, m);
		// If there is an empty clause
		if (flag == HaltFlag::empty_clause) {
			#ifdef DEBUG_PRINTS
			fprintf(stderr, "  Found empty clause\n");
			#endif
			while (!m.empty()) {
				auto x = m.back();
				m.pop_back();
				#ifdef DEBUG_PRINTS
				fprintf(stderr, "  Popped %d/%d\n", x.first, x.second);
				#endif

				// If decision literal
				if (x.second == false) {
					// Negate and add as deduced literal
					x.first *= -1;
					x.second = true;
					#ifdef DEBUG_PRINTS
					fprintf(stderr, "  Pushed %d/%d\n", x.first, x.second);
					#endif
					m.push_back(x);
					break;
				}
			}
			// If it reaches here then it's not possible to backtrack anymore
			if (m.empty()) {
				return false;
			}
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
				if (find_if(m.begin(), m.end(), [i](auto x){return x.first == i || x.first == -i;}) == m.end()) {
					#ifdef DEBUG_PRINTS
					fprintf(stderr, "  Adding %d\n", i);
					#endif
					m.push_back(make_pair(i, false));
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
	#ifdef DEBUG_PRINTS
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

	#ifdef DEBUG_PRINTS
	print_formula(f, stderr);
	#endif

	bool result = dpll(f, m, nvars);

	printf("%s", result ? "SATISFIABLE\n" : "UNSATISFIABLE\n");

	return 0;
}