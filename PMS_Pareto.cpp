/* 
 * Program to implement a Partial Max SAT solver
 * branch and bound method
 */

#include <iostream>
#include <algorithm>
#include <cmath>
#include <string>
#include <vector>
#include <ctime>
using namespace std;

const int inf = 0x3f3f3f3f; // value of infinite 

/*
 * enum for different types of return flags defined
 */
enum Cat {
    // in PMSAT Function as unit_propagate and apply_transform 
    satisfied,  // when a satisfying assignment has been found
    unsatisfied,// when no satisfying assignment has been found after
			    // exhaustively searching
    normal,		// when no satisfying assignment has been found till now, and DPLL()
				// has exited normally
    
    // in Pareto Function to represent dominate relationship
    dominating,    // A dominate B
    dominated,     // A is dominted by B
    nondominated,  // there is none dominated relationship between A and B
};

/*
 * class to represent a boolean formula
 */
class Formula {
public:
    // a vector that stores the value assigned to each variable, where
    // -1 - unassigned
    // 0 - true
    // 1 - false
    vector<int> literals;
	
	// vector to store the number of occurrences of each literal
    vector<int> literal_frequency; 

    // vector to store the difference in number of occurrences with
    // positive and negative polarity of each literal
    vector<int> literal_polarity;

    // vector to store the clauses
    // for each clauses, if the variable n is of positive polarity, then 2n is
    // stored if the variable n is of negative polarity, then 2n+1 is stored here,
    // n is assumed to be zero indexed
    // clauses[0] - hard clauses
    // clauses[1] - soft clauses
    vector<vector<int> > clauses[2];

    // last version regarded the cost of each clause as 1
    // In this version, we use soft_clause_cost to store the cost of each soft clause
    vector<vector<int> > soft_clause_cost;

    // vector to sore the number of optimal soft clauses cost in every branch
    // if formula is satisified
    vector<int> opt_cost;

    // vector to store the num of sum of removed soft clauses cost
    vector<int> remove_cost;

    // the number of sum of soft clause in the formula
    vector<int> sum_soft_cost;              

    Formula() {}

    // copy constructor for copying a formula - each member is copied over
    Formula(const Formula &f) {
        literals = f.literals;
        clauses[0] = f.clauses[0];
        clauses[1] = f.clauses[1];
        literal_frequency = f.literal_frequency;
        literal_polarity = f.literal_polarity;
        soft_clause_cost = f.soft_clause_cost;
        opt_cost = f.opt_cost;
        remove_cost = f.remove_cost;
        sum_soft_cost = f.sum_soft_cost;
    }

    // set the vectors to their appropriate sizes and initial values
    void initialize(int, int, int, int);
    
    // set the literate over the clauses
    void input(int, int, int);
};


void Formula:: initialize(int literal_count, int hard_clause_count, 
        int soft_clause_count, int cost_category_count){
    
    literals.clear();					// vector for literal
    literals.resize(literal_count, -1); 
    
    clauses[0].clear();				    // vector for hard clauses
    clauses[0].resize(hard_clause_count);
        
    clauses[1].clear();				    // vector for soft clauses
    clauses[1].resize(soft_clause_count);
     
    literal_frequency.clear();
    literal_frequency.resize(literal_count, 0);
     
    literal_polarity.clear();
    literal_polarity.resize(literal_count, 0);
    
    soft_clause_cost.clear();
    soft_clause_cost.resize(cost_category_count);
    for(int i = 0; i < cost_category_count; i++){
        soft_clause_cost[i].resize(soft_clause_count);
    }
    
    opt_cost.clear();
    opt_cost.resize(cost_category_count, 0);

    remove_cost.clear(); 
    remove_cost.resize(cost_category_count, 0);

    sum_soft_cost.clear();
    sum_soft_cost.resize(cost_category_count, 0);
}

void Formula::input(int hard_clause_count, int soft_clause_count, int cost_category_count){
    int literal; // store the incoming literal value
    // a array that store clause count  
    // 0 - hard clause 1 - soft clause
    int count[2] = {hard_clause_count, soft_clause_count}; 
    
    for(int i = 0; i < cost_category_count; i++) {
        for(int j = 0; j < soft_clause_count; j++){
            cin >> soft_clause_cost[i][j];   // cost of each soft clause
            sum_soft_cost[i] += soft_clause_cost[i][j];
        }
    }
    
    for (int p = 0; p < 2; p++) { // point for hard or soft clause
        for (int i = 0; i < count[p]; i++) {
            while (true) { // while the ith clause gets more literals
                cin >> literal;
                if (literal > 0) { // if the variable has positive polarity
                    // store it in the form 2n
                    clauses[p][i].push_back(2 * (literal - 1));
                    // increment frequency and polarity of the literal
                    literal_frequency[literal - 1]++;
                    literal_polarity[literal - 1]++;
                } else if (literal < 0) { // if the variable has negative polarity
                    // store it in the form 2n+1
                    clauses[p][i].push_back(2 * ((-1) * literal - 1) + 1);
                    // increment frequency and decrement polarity of the literal
                    literal_frequency[-1 - literal]++;
                    literal_polarity[-1 - literal]--;
                } else {
                     break; // read 0, so move to next clause
                }
            }
        }
    }
}


/*
 * class to represent the structure and functions of the SAT solver
 */
class PMSATSolver{
private: 
	int literal_count;				// the number of variables in the formula
	Formula formula;			    // the initial hard and soft formula
	int hard_clause_count;			// the number of hard clauses in the formula
	int soft_clause_count;			// the number of soft clauses in the formula
    int cost_category_count;        // the bumber of cost categories in the formula
    vector<Formula> pareto_front;   // preto front set
	
	int unit_propagate(Formula &);	// performs unit propagation
	int apply_transform(Formula &, int);// applies the value of the literal
    void PMSAT(Formula);        // performs branch and bound methods recursively

    // performs remove satisfied clauses or unsatisfied clauses
    int judge_clause(Formula &, int &, int &, int &, bool);
    int judge_pareto(Formula, Formula);// judge dominate relationship between formulas 
    bool judge_purning(Formula);    // judge the purning process

	void display(Formula &, int);	// display the result
    void add_answer(Formula);
    void print_answer();

public:
	PMSATSolver() {}
	void initialize();			    // initializes the values
	void solve();				    // calls the solver
};

/*
 * function that accepts the inputs from the user and initializes the attributes
 * in the solver
 */
void PMSATSolver::initialize() {
    char c;   // store first character
    string s; // dummy string

    while (true) {
        cin >> c;
        if (c == 'c') {         // if comment
            getline(cin, s);    // ignore
        } else {                // else, if would be a p
            cin >> s;           // this would be cnf
            break;
        }
    }
    cin >> literal_count;
    cin >> hard_clause_count;
	cin >> soft_clause_count;
    cin >> cost_category_count;

    pareto_front.clear();

	formula.initialize(literal_count, hard_clause_count, soft_clause_count,
            cost_category_count);
	
	formula.input(hard_clause_count, soft_clause_count, cost_category_count);
}

/*
 * function to perform unit resolution in a given formula
 * arguments: f - the formula to perform unit resolution on
 * return value: int - the status of the solver after unit resolution, a member
 * of the Cat enum Cat::satisfied - both hard and soft formula has been satisfied
 *                 Cat::unsatisfied - the formula can no longer be satisfied
 *                 Cat::normal - normal exit
 */
int PMSATSolver::unit_propagate(Formula &f) {
    if(f.clauses[0].size() == 0 && f.clauses[1].size() == 0){
        return Cat::satisfied;
    }
    // stores whether the current iteration found a unit clause
    bool unit_clause_found = false; 
    if (f.clauses[0].size() == 0 && f.clauses[1].size() == 0) {	
        // if the formula contains no clauses
        // display(f, Cat::satisfied);
        return Cat::satisfied;		// it is vacuously satisfied
    }
    do {
        unit_clause_found = false;
        // iterate over only the hard clauses in f
        for (int i = 0; i < f.clauses[0].size(); i++) {
            // if the size of a clause is 1, it is a unit clause
            if (f.clauses[0][i].size() == 1) { 
                unit_clause_found = true;
                // 0 - if true, 1 - if false, set the literal
                f.literals[f.clauses[0][i][0] / 2] = f.clauses[0][i][0] % 2; 
                // once assigned, reset the frequency to mark it closed
                f.literal_frequency[f.clauses[0][i][0] / 2] = -1; 
                // apply this change through f
                int result = apply_transform(f, f.clauses[0][i][0] / 2); 
                // if this caused the formula to be either satisfied 
                // or unsatisfied, return the result flag
                if (result == Cat::satisfied || result == Cat::unsatisfied) {
                    return result;
                }
                break; // check for another unit clause from start
            } 
            // else if (f.clauses[p][i].size() == 0) { // ????
            //     // if a given clause is empty
            //     return Cat::unsatisfied; // unsatisfiable in this branch
            // }
            // continue do-whiile loop to check for another unit clause from start
            if(unit_clause_found) break;
        } 
    } while (unit_clause_found);

    return Cat::normal; // if reached here, the unit resolution ended normally
}

/*
 * applies a value of a literal to all clauses in a given formula
 * arguments: f - the formula to apply on
 *            literal_to_apply - the literal which has just been set
 * return value: int - the return status flag, a member of the Cat enum
 *               Cat::satisfied - both hard and soft formula has been satisfied
 *               Cat::unsatisfied - the formula can no longer be satisfied
 *               Cat::normal - normal exit
 */
int PMSATSolver::apply_transform(Formula &f, int literal_to_apply) {
    // the value to apply, 0 - if true, 1 - if false
    int value_to_apply = f.literals[literal_to_apply]; 
    for (int p = 0; p < 2; p++) {
        // iterate over the hard clauses in f
        for (int i = 0; i < f.clauses[p].size(); i++) {
            // iterate over the variables in the clause
            for (int j = 0; j < f.clauses[p][i].size(); j++) {
                // if this is true, then the literal appears with the same polarity 
                // as it is being applied that is, if assigned true, it appears 
                // positive if assigned false, it appears negative, in this clause 
                // hence, the clause has now become true
                if ((2 * literal_to_apply + value_to_apply) == f.clauses[p][i][j]) {
                    int judge_result = judge_clause(f, p, i, j, true);
                    if(judge_result == Cat::satisfied || judge_result == Cat::unsatisfied){
                        return judge_result;
                    }
                    break; // move to the next clause
                } else if (f.clauses[p][i][j] / 2 == literal_to_apply) {
                    int judge_result = judge_clause(f, p, i, j, false);
                    if(judge_result == Cat::satisfied || judge_result == Cat::unsatisfied){
                        return judge_result;
                    }
                    break; // move to the next clause
                }
            }
        }
    }
    // if reached here, the function is exiting normally
    return Cat::normal;
}

/*
 * Function to judge pareto relationship between two Formulas
 * arguments - f1 & f2 two formulas
 * return value:  Cat::dominating   f1 is dominating f2
 *                Cat::dominated    f1 is dominted by f2
 *                Cat::nondominated there is no dominted relationship
 */
int PMSATSolver::judge_pareto(Formula f1, Formula f2) {
    int cnt1 =0, cnt2 = 0;
    // upd: in this version, if f1 & f2 have same opt_cost for all cost categories
    // function will return f1 dominate f2 to make sure there will be only one formula
    // with these value in pareto front
    for(int i = 0; i < cost_category_count; i++){
        if(f1.opt_cost[i] >= f2.opt_cost[i]) cnt1++;
        if(f1.opt_cost[i] <= f2.opt_cost[i]) cnt2++;
    }

    if(cnt1 == cost_category_count){
        return Cat::dominating;
    } else if(cnt2 == cost_category_count){
        return Cat::dominated;
    } else {
        return Cat::nondominated;
    }
}

int PMSATSolver::judge_clause(Formula &f, int &p, int &i, int &j, bool flag){
    if(flag){
        // remove the satisfied clause from the list
        f.clauses[p].erase(f.clauses[p].begin() + i); 
        if (p == 1){  // soft clause
            for(int k = 0; k < cost_category_count; k++){
                // add clause cost to opt_cost
                f.opt_cost[k] += f.soft_clause_cost[k][i];
                // remove the clause cost from the list
                f.soft_clause_cost[k].erase(f.soft_clause_cost[k].begin() + i);
            }
        }
        i--;                // reset iterator
    } else {
        // the literal appears with opposite polarity 
        // remove the literal from the clause, as it is false in it
        f.clauses[p][i].erase(f.clauses[p][i].begin() + j); 
        j--;    // reset the iterator
        if (f.clauses[p][i].size() == 0) {
            if(p == 0){
                // if the hard clause is empty
                // formula is unsatisfiable currently
                return Cat::unsatisfied;
            }  else {
                f.clauses[p].erase(f.clauses[p].begin() + i);
                for(int k = 0; k < cost_category_count; k++){
                    // remove the clause from list
                    // add clause cost to remove cost
                    f.remove_cost[k] += f.soft_clause_cost[k][i];
                    // remove the clause cost from the list
                    f.soft_clause_cost[k].erase(f.soft_clause_cost[k].begin() + i);
                }
                i--;
            }
        }
    }
    // if all hard and soft clauses have been removed
    if (f.clauses[0].size() == 0 && f.clauses[1].size() == 0 ) { 
        return Cat::satisfied;  // the formula is satisfied
    }
    return Cat::normal;
}

/*
 * Function to jduge if this current node with formula f 
 * with the max cost may dominate any solution in pareto front
 */
bool PMSATSolver::judge_purning(Formula f) {
    if(pareto_front.empty()) {
        return true;
    }
    for(int i = 0; i < pareto_front.size(); i++){
        for(int k = 0; k < cost_category_count; k++){
            int max_cost = f.sum_soft_cost[k] - f.remove_cost[k];
            // upd: in this version only max_cost is larger than 
            // any solution in pareto_front
            if(max_cost > pareto_front[i].opt_cost[k]){
                return true;
            }
        }
    }
    return false;
}

/*
 * Function to judge if a feasible solution f can be added in pareto_front
 */
void PMSATSolver::add_answer(Formula f){
    // if this is the first feasible solution add it to pareto_front
    if (pareto_front.empty()) {
        pareto_front.push_back(f);
        return;
    }
    bool flag = true; // to represent if f is nondominated 
    for(int i  = 0; i < pareto_front.size(); i++) {
        // judge f with every feasible solution in pareto front
        int judge_result = judge_pareto(f, pareto_front[i]);
        // upd: in this version, for different solution with same value of each 
        // cost categories, we only add one in pareto front
        if(judge_result == Cat::dominating) {
            // if f is dominating a solution in pareto_front remove it
            pareto_front.erase(pareto_front.begin() + i);
            i--;
        } else if(judge_result == Cat::dominated){
            flag = false;
            // if formula f is dominated by any solution in pareto front
            // named f2, it means every solution in pareto front is nondominated by
            // f2, hence that is nondominated by f
            break; 
        }
    }
    if(flag == true){
        pareto_front.push_back(f);
    }
}

/*
 * Function to display literal satisfied or unsatisfied
 * arguments: f - formula 
 *            result - satisfied or unsatisfied
 */
void PMSATSolver::display(Formula &f, int result) {
    cout << endl << "******** display ***********" << endl;
    if (result == Cat::satisfied) { // if the formula is satisfiable
        cout << "SAT" << endl;
        for (int i = 0; i < f.literals.size(); i++) {
            if (f.literals[i] != -1) {
                cout << pow(-1, f.literals[i]) * (i + 1) << " ";
            } else {  
                // for literals which can take either value, 
                // arbitrarily assign them to be true
                cout << (i + 1) << " ";
            }
        }
        cout << "0" << endl; 
        
        cout << "costs:";
        for(int i = 0; i < cost_category_count; i++) {
            cout << " " << f.opt_cost[i];
        }
        cout << endl;
    } else { // if the formula is unsatisfiable
        cout << "UNSAT";
    }
    cout << "****************************" << endl << endl;
}

/* 
 * function to perform the branch and bound method on a given formula
 * argument: formula - the formula to perform branch and bound method on
 *           lower_bound - value of optimal complete solution initialized to inf
 * return value: int - value of optimal complete solution
 *               inf - no satisfiable solution
 */
void PMSATSolver::PMSAT(Formula f){
    // purning process
	// lower_bound is the optimalcomplete solution initialized to -inf
	// upper_bound is number of empty clause in f at most
    // int upper_bound = ;
    // if(upper_bound <= lower_bound) return lower_bound;
   
    int result = unit_propagate(f); // perform unit propagation on the formula 
    
    if(result == Cat::satisfied) {  // if satisfied, show result and return
        // int ans = f.opt_cost;
        // display(f, result);
        // return ans;         // answer is lower bound 
        add_answer(f); 
        return;
    } else if(result == Cat::unsatisfied) { // if hard clauses not satisfied
        return;                // return -inf
    }

    if(judge_purning(f) == false) { // purning process
        return;
    }  
    
    // find the variable with maximum frequency in f, which will be the next to be
    // assigned a value already assigned variables have this field reset to -1 in
    // order to ignore them
    int i = distance(f.literal_frequency.begin(), 
            max_element(f.literal_frequency.begin(), f.literal_frequency.end()));
    // need to apply twice, once true, the other false
    for (int j = 0; j < 2; j++) {
        Formula new_f = f; // copy the formula before recursing
        new_f.literals[i] = j;  // assign positive first
        new_f.literal_frequency[i] = -1; 
        // reset the frequency to -1 to ignore in the future
        int transform_result = apply_transform(new_f, i); 

        // int ret = new_f.opt_cost;
        // apply the change to all the clauses
        if (transform_result == Cat::satisfied) { 
            // if formula satisfied both hard and soft clause
            // meas all literal has been selected
            // display(new_f, transform_result);
            add_answer(new_f);
            // lower_bound = max(lower_bound);
        } else if(transform_result == Cat::unsatisfied) {
            continue;
        } else if(transform_result == Cat::normal) {
            PMSAT(new_f);
        }
    }
    // return lower_bound;
}

void PMSATSolver::print_answer() {
    cout << endl << "******** answer ***********" << endl;
    if(pareto_front.empty()) {
        cout << "UNSAT" << endl;
    }
    for(int i = 0; i < pareto_front.size(); i++){
        cout << "SAT: " << (i + 1) << endl;
        Formula f = pareto_front[i];
        for (int i = 0; i < f.literals.size(); i++) {
            if (i != 0) {
                cout << " ";
            }
            if (f.literals[i] != -1) {
                cout << pow(-1, f.literals[i]) * (i + 1);
            } else {  
                // for literals which can take either value, 
                // arbitrarily assign them to be true
                cout << (i + 1);
            }
        }
        cout << " 0" << endl; 
        cout << "Costs: ";
        for(int i = 0; i < cost_category_count; i++){
            cout << " " << f.opt_cost[i];
        }
        cout << endl;
    }
    cout << "***************************" << endl << endl;

}

void PMSATSolver::solve(){
    initialize();    // initialize
    clock_t startTime,endTime;
    PMSAT(formula);
    endTime = clock();
    print_answer();
    cout << "The run time is: " <<(double)(endTime - startTime) / CLOCKS_PER_SEC << "s" << endl;
}

int main() {
    PMSATSolver solver;     // create the solver
    solver.solve();         // solve
    return 0;
}

