# Multi-objective Optimization Pareto-front for PMSAT

Program to implement a Partial Max SAT solver

Multi-objective Optimization Pareto-Front

## Cat

用 $enum$ 存放函数的返回状态，其中

**satisfied**  - 用于表示 PMS 中 hard clauses 全部满足，以及 soft clauses 全部验证完毕的状态

**unsatisfied** - 用于表示在求解过程中，出现 hard clause 为 false 的情况，此时求解不应继续进行下去

**normal** - 用于表示求解过程中正常的退出，即仍有子句未满足，无 hard clause 冲突

**dominating** - 用于表示两个可行解的 Pareto 关系为，A 支配 B

**dominated** - 用于表示两个可行解的 Pareto 关系为，B 支配 A

**nondominated** - 用于表示两个可行解，没有支配关系

## Formula

用于存放 PMS 实例的类，其中

```C++
vector<int> literals;
```

用于表示变量的取值，-1表示未赋值，0-true，1-false

```C++
vector<int> literal_frequency; 
```

用于表示变量出现的频率，贪心的选出出现次数最多的变量，这样赋值后影响的语句更多，有利于剪枝

```C++
vector<int> literal_polarity;
```

用于记录当前变量以 $x_i$ 状态出现的多，还是以 $\neg x_i$ 状态出现的多，我们考虑优先给 $x_i$ 赋值 true or false

```C++
vector<vector<int> > clauses[2];
```

用于存放 hard clauses - clauses[0] 和 soft clauses - clauses[1]，通过下标关联方便遍历

```c++
vector<vector<int> > soft_clause_cost;
```

用于记录第 i 条软子句的，第 k 种目标开销的花费。soft_clause_cost\[k\]\[i\]  

```C++
vector<int> opt_cost;
```

用于记录，当前变量分配情况下，k种目标开销的最佳花费（最大）

```C++
vector<int> remove_cost;
```

用于记录当前状态的 Formula 中，移除的、不满足条件的 soft clause 的第k种花费

```C++
vector<int> sum_soft_cost; 
```

用于记录，第k种目标花费所有的软子句的cost之和

```C++
void initialize(int literal_count, int hard_clause_count, int soft_clause_count, int cost_category_count){}
```

用于初始化 Formula 的大小和初值

```C++
void input(int hard_clause_count, int soft_clause_count, int cost_category_count){}
```

用于读入 hard clauses 和 soft clauses，以及soft clauses 的所有k种花费

## PMSATSolver

求解 PMS 问题所用的相关变量和函数

```C++
int literal_count;
Formula formula;
int hard_clause_count;
int soft_clause_count;
int cost_category_count;
vector<Formula> pareto_front;
```

用于存放相关变量的数值，pareto_front储存了所有的pareto前沿，在当前版本中，对于所有k种花费均相同的情况，保留了所有的可行解

```C++
int unit_propagate(Formula &);
```

对一个 Formula 中的 **hard clauses** 部分进行单元传播，即对于子句中仅有一个变量的句子，我们可以确定它的取值。由于 soft clauses 可以不被满足，我们只求满足的最大值，所以 soft clauses 不适用于此。 ($Unit Propagate rule$)

unit_propagate 的返回值如 Cat 中定义的那样，用来表示 当前实例状态，包括 satisfied、unsatisfied、normal

```C++
int apply_transform(Formula &, int);
```

对于我们确定下某个变量的取值后，我们应将这个取值应用在 Formula 中，应用时，对于包括当前变量的子句，有以下两种状态

1. 满足当前子句为真 - 已满足该子句，从 clauses 中删除，即为 empty_clause 状态
2. 不满足当前子句 - 从该子句中删除当前变量，若此时该子句为空，又考虑：
   - 若该子句为 hard clause，则立即返回 unsatisfied
   - 若该子句为 soft clause，则应使 remove_count++;

```C++
int judge_pareto(Formula, Formula);
```

判断两个可行解的pareto关系，A 支配 B，B 支配 A 或者 A 和 B 没有支配关系。当前版本中，若 A 和 B 在 k 种 cost 上的最佳值均相同，会同时保留两种解。

```C++
int judge_clause(Formula &f, int &p, int &i, int &j, bool flag);
```

由于多加了一维 k 表示 k 种不同的花费，所以将 apply_transform 当中对于clause的操作模块化出来。主要为对满足条件的子句的删除，如果是软子句则记录它的cost。对不满足的子句删除对应的元素，如果此时子句为空，则删除该子句，若删除的子句是hard clause，则不满足条件，应当返回 unsatisfied。

```C++
int PMSAT(Formula, int);
```

递归求解的程序，使用 Branch and Bound method，在解答树上进行 DFS，算法的结构如下

> **Algorithm**  PMSAT(f)
>
> **Input: ** f - PMSAT 实例
>
> **Algorithm：**
> 
>unit\_propagate(f)
> 
>**if**  satisfied  **then** add_answer(f) **return** 
> 
> **if**  unsatisfied **then return**   
> 
> l = select_variable  选出一个变量 l
> 
> apply_transform
> 
> PMSAT(f_l,lower\_bound)​   PMSAT(f_{\bar{l}}, lower_bound)​   (分支)
> 
> **return** $\max$ 
> 


```C++
void display(Formula &, int);
```

打印实例是否被满足，如果满足则打印 Assignment

在当前程序版本中，在解答树的叶子节点上，打印了当前可行解，用于判断剪枝是否成功以及当前程序的正确性。最终版本需要删除

```C++
void add_answer(Formula f);
```

判断可行解能否加入到 pareto_front 当中，此版本在这里使用的是暴力判断，遍历当前 pareto_front 当中所有解和当前可行解的关系，如果当前可行解支配pareto 中的解，则删除该解，如果当前可行解被pareto_front 中的解支配，则标记当前解不加入pareto_front。最后若未被标记，则将当前可行解加入pareto_front。

```C++
void print_answer();
```

打印 pareto_front 中的所有解。

```C++
void initialize();
```

用于初始化

```C++
void solve();
```

封装的解答程序
