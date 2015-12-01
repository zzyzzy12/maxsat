/* Based on maxsatz1.c, including look ahead further on unit clauses
 */
/*based on maxsatz5.c, moving lookahead before branching (instead of after
in maxsatz5.c
*/

/*based on maxsatz8.c, integrating resolution rule:

if x or y and x or ¬y are clauses, then remove these two binary clauses
and add the unit clause x

*/

/* based on maxsatz9.c, integrating advanced so-called star rule:

if x, y and ¬x or ¬y are clauses then remove these three clauses, increment
NB_EMPTY by 1 and add clause x or y.

*/
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include <sys/times.h>
#include <sys/types.h>
#include <limits.h>

#include <iostream>
#include <cstdio>
#include <cstring>
#include <algorithm>
#include <cmath>
#include <map>
#include <set>
#include <queue>
#include <stack>
using namespace std;

typedef signed char my_type;
typedef unsigned char my_unsigned_type;

#define WORD_LENGTH 100 
#define TRUE 1
#define FALSE 0
#define NONE -1

#define WEIGHT 4
#define WEIGHT1 25
#define WEIGHT2 5
#define WEIGHT3 1
#define T 10

/* the tables of variables and clauses are statically allocated. Modify the 
   parameters tab_variable_size and tab_clause_size before compilation if 
   necessary */
#define tab_variable_size  2000   //原始的是20000
#define tab_clause_size 4000   //原始的是40000
#define tab_unitclause_size \
 ((tab_clause_size/4<2000) ? 2000 : tab_clause_size/4)
#define my_tab_variable_size \
 ((tab_variable_size/2<1000) ? 1000 : tab_variable_size/2)
#define my_tab_clause_size \
 ((tab_clause_size/2<2000) ? 2000 : tab_clause_size/2)
#define my_tab_unitclause_size \
 ((tab_unitclause_size/2<1000) ? 1000 : tab_unitclause_size/2)
#define tab_literal_size 2*tab_variable_size
#define double_tab_clause_size 2*tab_clause_size
#define positive(literal) literal<NB_VAR
#define negative(literal) literal>=NB_VAR
#define get_var_from_lit(literal) \
  ((literal<NB_VAR) ? literal : literal-NB_VAR)
#define complement(lit1, lit2) \
 ((lit1<lit2) ? lit2-lit1 == NB_VAR : lit1-lit2 == NB_VAR)

#define inverse_signe(signe) \
 (signe == POSITIVE) ? NEGATIVE : POSITIVE
#define unsat(val) (val==0)?"UNS":"SAT"
#define _pop(stack) stack[--stack ## _fill_pointer]
#define _push(item, stack) stack[stack ## _fill_pointer++] = item
#define satisfiable() CLAUSE_STACK_fill_pointer == NB_CLAUSE

#define NEGATIVE 0
#define POSITIVE 1
#define PASSIVE 0
#define ACTIVE 1 
#define DONE -1
//-------------DEBUG--------------
#define DEBUG_OPEN_RULE3 true
#define DEBUG_OPEN_RULE4 false
#define DEBUG_OPEN_RULE6 true
#define MAX_N_SAT 4
//--------------------------------

int *neg_in[tab_variable_size];
int *pos_in[tab_variable_size];
int neg_nb[tab_variable_size];
int pos_nb[tab_variable_size];
my_type var_current_value[tab_variable_size];
my_type var_rest_value[tab_variable_size];
my_type var_state[tab_variable_size];

int saved_clause_stack[tab_variable_size];
int saved_reducedclause_stack[tab_variable_size];
int saved_unitclause_stack[tab_variable_size];
int saved_nb_empty[tab_variable_size];
int my_unitclause_process(int starting_point);
int simple_get_pos_clause_nb(int var) ;
int simple_get_neg_clause_nb(int var) ;
bool judgeClauseAndVar(); //自己提上来的
int assign_value(int var, int current_value, int rest_value); //自己提上来的
void outputLit(int c); //自己提上来的
my_unsigned_type nb_neg_clause_of_length1[tab_variable_size];
my_unsigned_type nb_pos_clause_of_length1[tab_variable_size];
my_unsigned_type nb_neg_clause_of_length2[tab_variable_size];
my_unsigned_type nb_neg_clause_of_length3[tab_variable_size];
my_unsigned_type nb_pos_clause_of_length2[tab_variable_size];
my_unsigned_type nb_pos_clause_of_length3[tab_variable_size];

float reduce_if_negative[tab_variable_size];
float reduce_if_positive[tab_variable_size];

int *sat[tab_clause_size];
int *var_sign[tab_clause_size];
my_type clause_state[tab_clause_size];
my_type clause_length[tab_clause_size];

int VARIABLE_STACK_fill_pointer = 0;
int CLAUSE_STACK_fill_pointer = 0;
int UNITCLAUSE_STACK_fill_pointer = 0;
int REDUCEDCLAUSE_STACK_fill_pointer = 0;


int VARIABLE_STACK[tab_variable_size];
int CLAUSE_STACK[tab_clause_size];
int UNITCLAUSE_STACK[tab_unitclause_size];
int REDUCEDCLAUSE_STACK[tab_clause_size];

int PREVIOUS_REDUCEDCLAUSE_STACK_fill_pointer = 0;

int NB_VAR;
int NB_CLAUSE;
int INIT_NB_CLAUSE;
int REAL_NB_CLAUSE;

long NB_UNIT=1, NB_MONO=0, NB_BRANCHE=0, NB_BACK = 0;
int NB_EMPTY=0, UB;

#define NO_CONFLICT -3
#define NO_REASON -3
int reason[tab_variable_size];
int REASON_STACK[tab_variable_size];
int REASON_STACK_fill_pointer=0;
set<int> recur[tab_variable_size]; // 新加的...为了做递推
int MY_UNITCLAUSE_STACK[tab_variable_size];
int MY_UNITCLAUSE_STACK_fill_pointer=0;
int CANDIDATE_LITERALS[2*tab_variable_size];
int CANDIDATE_LITERALS_fill_pointer=0;
int NEW_CLAUSES[tab_clause_size][20];  //大小注意
int NEW_CLAUSES_fill_pointer=0;
int lit_to_fix[tab_clause_size];
int *SAVED_CLAUSE_POSITIONS[tab_clause_size];
int SAVED_CLAUSES[tab_clause_size];
int SAVED_CLAUSES_fill_pointer=0;
int lit_involved_in_clause[2*tab_variable_size];
int INVOLVED_LIT_STACK[2*tab_variable_size];
int INVOLVED_LIT_STACK_fill_pointer=0;
int fixing_clause[2*tab_variable_size];
int saved_nb_clause[tab_variable_size];
int saved_saved_clauses[tab_variable_size];
int saved_new_clauses[tab_variable_size];

#include "input.c" 

void outputClauseAndlit(int lit,int sign,int clause){
  puts("-----output Clause and lit relationship----");
  int *clauses;
  if (sign==POSITIVE) clauses=pos_in[lit];
                else  clauses=neg_in[lit]; 
  for (int c=*clauses;c!=NONE;c=*(++clauses)) 
      if (clause_state[c]==ACTIVE)
          printf("C%d ",c);
  puts("");
  int *vars_signs=var_sign[clause];
  for (int var=*(vars_signs);var!=NONE;var=*(vars_signs+=2)){
      if (var_state[var]!=ACTIVE) continue;
      if (*(vars_signs+1)==POSITIVE) printf("X%d ",var);
                                else printf("-X%d ",var);
  }
  puts("");
  puts("-----output Clause and lit relationship----");
}

void remove_clauses(int var) {  //将与var赋值后确定可以满足的clause标记删去
  register int clause;
  register int *clauses;
  if (var_current_value[var] == POSITIVE) clauses = pos_in[var]; // pos_in[var]存与var相关的clause标号，若当前的var是1则将所有包涵var的clause删去
  else clauses = neg_in[var]; // neg_in[var]存与var相关的clause标号，若当前的var是0则将所有包涵¬var的clause删去
  for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if (clause_state[clause] == ACTIVE) { //这个clause还是active的
      clause_state[clause] = PASSIVE;
      _push(clause, CLAUSE_STACK); //把这些删去的clause压到栈CLAUSE_STACK中
    }
  }
}

int reduce_clauses(int var) { //将与var赋值后确定还不一定满足的clause中的var标记删去
  register int clause;
  register int *clauses;
  if (var_current_value[var] == POSITIVE) clauses = neg_in[var]; // 若当前的var是1则将所有包涵¬var的clause中的¬var删去
  else clauses = pos_in[var];  // 若当前的var是0则将所有包涵var的clause中的var删去
  for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if (clause_state[clause] == ACTIVE) {
      clause_length[clause]--; // 长度可以－1了
      _push(clause, REDUCEDCLAUSE_STACK);
      switch (clause_length[clause]) { //看长度的情况
      case 0: NB_EMPTY++;      
  if (UB<=NB_EMPTY) return NONE;  //这种情况下才返回NONE
  break;
      case 1:       //长度为1则是unit
  _push(clause, UNITCLAUSE_STACK); //将这些clause放入UNITCLAUSE_STACK中
  break;
      }
    }
  }
  return TRUE;
}

int my_reduce_clauses(int var) {  //细分reduce_clauses操作
  register int clause;
  register int *clauses;
  if (var_current_value[var] == POSITIVE) clauses = neg_in[var]; // 若当前的var是1则将所有包涵¬var的clause中的¬var删去
  else clauses = pos_in[var];  // 若当前的var是0则将所有包涵var的clause中的var删去
  for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if (clause_state[clause] == ACTIVE) {
      clause_length[clause]--;
      _push(clause, REDUCEDCLAUSE_STACK);
      switch (clause_length[clause]) {
      case 0: return clause; //长度为空
      case 1: 
  _push(clause, MY_UNITCLAUSE_STACK); //MY_UNITCLAUSE_STACK要干嘛？
  break;
      }
    }
  }
  return NO_CONFLICT;
}

int my_reduce_clauses_for_fl(int var) { //细分reduce_clauses操作
  register int clause;
  register int *clauses;
  if (var_current_value[var] == POSITIVE) clauses = neg_in[var]; //把与其相关的clause都拿出来
  else clauses = pos_in[var];
  for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if (clause_state[clause] == ACTIVE) {  //该clause是active的才处理
      clause_length[clause]--;
      _push(clause, REDUCEDCLAUSE_STACK);
      switch (clause_length[clause]) {
      case 0: return clause;  //clause为空了
      case 1: 
  _push(clause, UNITCLAUSE_STACK);  //成为了unit_clause
  break;
      }
    }
  }
  return NO_CONFLICT;
}

void print_values(int nb_var) { //输出解
  FILE* fp_out;
  int i;
  fp_out = fopen("satx.sol", "w");
  for (i=0; i<nb_var; i++) {
    if (var_current_value[i] == 1)  // possive
      fprintf(fp_out, "%d ", i+1);  
    else
      fprintf(fp_out, "%d ", 0-i-1);
  }
  fprintf(fp_out, "\n");
  fclose(fp_out);     
} 

int backtracking() {  //进行回朔
  int var, index,clause, *position, saved;
      
  NB_BACK++;  

  do {
    var = _pop(VARIABLE_STACK); //把VARIABLE_STACK的一个个弹出来处理
    if (var_rest_value[var] == NONE)  
      var_state[var] = ACTIVE;
    else {
      for (index = saved_clause_stack[var]; index < CLAUSE_STACK_fill_pointer; index++)
         clause_state[CLAUSE_STACK[index]] = ACTIVE;
      CLAUSE_STACK_fill_pointer = saved_clause_stack[var];

      for (index = saved_reducedclause_stack[var]; index < REDUCEDCLAUSE_STACK_fill_pointer; index++) { 
         clause = REDUCEDCLAUSE_STACK[index];
         clause_length[REDUCEDCLAUSE_STACK[index]]++;
      }
      REDUCEDCLAUSE_STACK_fill_pointer = saved_reducedclause_stack[var];
      UNITCLAUSE_STACK_fill_pointer=saved_unitclause_stack[var];
      NB_EMPTY=saved_nb_empty[var];
      NB_CLAUSE=saved_nb_clause[var]; 
      NEW_CLAUSES_fill_pointer=saved_new_clauses[var];  //把之前位置给取回来
      
      saved=saved_saved_clauses[var];
      for (index = SAVED_CLAUSES_fill_pointer-1 ; index >= saved; index--) 
           *SAVED_CLAUSE_POSITIONS[index]=SAVED_CLAUSES[index]; //保存还原现场?
      SAVED_CLAUSES_fill_pointer=saved;  //更新SAVED_CLAUSES_fill_pointer

      if (NB_EMPTY<UB) {
          var_current_value[var] = var_rest_value[var]; 
          var_rest_value[var] = NONE;
          _push(var, VARIABLE_STACK);  // 把var压回去
          if (reduce_clauses(var)==NONE)  //将包涵var为0的clause中的var删去，在这个过程中可能产生不能满足的clause 会调整UB
                   return NONE;
         remove_clauses(var);  //把包涵var为1的clause删去
         return TRUE;
      }
      else
         var_state[var] = ACTIVE;
    }
  }while (VARIABLE_STACK_fill_pointer > 0); // VARIABLE_STACK中还有东西
  return FALSE;
}

int verify_solution(my_type *value) { //找出解的大小
  int i, nb=0, var, *vars_signs, clause_truth,cpt;

  for (i=0; i<REAL_NB_CLAUSE; i++) {  //下标从0开始
    clause_truth = FALSE;
    vars_signs = var_sign[i];
    for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) 
      if (*(vars_signs+1) == value[var] ) { //其赋值和其正负是相同的，就是1
          clause_truth = TRUE;   //有一个是1该clause就是1
          break;
      }
    if (clause_truth == FALSE) nb++; //把不满足的个数统计出来
  }
  return nb;
}

void reset_context(int saved_clause_stack_fill_pointer,int saved_reducedclause_stack_fill_pointer,
                   int saved_unitclause_stack_fill_pointer,int saved_variable_stack_fill_pointer) {  //重置一个什么? 还原现场?
  int index, var, clause;
  for (index = saved_clause_stack_fill_pointer; index < CLAUSE_STACK_fill_pointer; index++) //将删去的这一段还原
     clause_state[CLAUSE_STACK[index]] = ACTIVE;
  CLAUSE_STACK_fill_pointer = saved_clause_stack_fill_pointer;

  for (index = saved_reducedclause_stack_fill_pointer; index < REDUCEDCLAUSE_STACK_fill_pointer; index++) { //将调整了的clause还原长度
    clause = REDUCEDCLAUSE_STACK[index];  //取出值
    clause_length[REDUCEDCLAUSE_STACK[index]]++; //还原长度
  }
  REDUCEDCLAUSE_STACK_fill_pointer = saved_reducedclause_stack_fill_pointer;

  for(index=saved_variable_stack_fill_pointer;index<VARIABLE_STACK_fill_pointer;index++) { //将去掉的var还原
    var=VARIABLE_STACK[index];  //取出值
    reason[var]=NO_REASON; //一个标记
    var_state[var]=ACTIVE;
  }
  VARIABLE_STACK_fill_pointer=saved_variable_stack_fill_pointer;

  UNITCLAUSE_STACK_fill_pointer=saved_unitclause_stack_fill_pointer;
}

int replace_clause(int newclause, int clause_to_replace, int *clauses) { //把clause_to_replace替换成newclause
  int clause, flag=FALSE;
  int *c=clauses; //  
 // puts("ENTHER"); 
  //if (clauses==NULL) puts("~~~~");
  for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if (clause==clause_to_replace) { 
      *clauses=newclause;
      SAVED_CLAUSE_POSITIONS[SAVED_CLAUSES_fill_pointer]=clauses; //纪录一下被替换的是哪个位置
      _push(clause_to_replace, SAVED_CLAUSES); //存一下这个被替换的clause_to_replace
      flag=TRUE; //正常来说是一定可以找到的
      break;
    }
  }  
  if (flag==FALSE)  //正常来说是不可能出错的
  {
      *(clauses)=newclause,*(clauses+1)=NONE;
      SAVED_CLAUSE_POSITIONS[SAVED_CLAUSES_fill_pointer]=clauses;
      _push(NONE, SAVED_CLAUSES);
      flag=TRUE; 
      //printf("problem...replace_clause\n");  
  } 
 // puts("OUT");
  return flag;
}

void create_binaryclause(int var1, int sign1, int var2, int sign2,int clause1, int clause2) {  //创建两元的clause
  int *vars_signs, *clauses1, *clauses2;
  if (sign1==POSITIVE) clauses1=pos_in[var1]; else clauses1=neg_in[var1]; //正的还是负的，把其数组拿出来
  if (sign2==POSITIVE) clauses2=pos_in[var2]; else clauses2=neg_in[var2]; //正的还是负的，把其数组拿出来
  vars_signs=NEW_CLAUSES[NEW_CLAUSES_fill_pointer++]; //新分配一个clause
  if (var1<var2) { //按照顺序来放
    vars_signs[0]=var1; vars_signs[1]=sign1;
    vars_signs[2]=var2; vars_signs[3]=sign2;
  }
  else {
    vars_signs[0]=var2; vars_signs[1]=sign2;
    vars_signs[2]=var1; vars_signs[3]=sign1;
  }
  vars_signs[4]=NONE;  //结束符号
  var_sign[NB_CLAUSE]=vars_signs; //clause中元素的情况
  clause_state[NB_CLAUSE]=ACTIVE; //clause本身为激活状态
  clause_length[NB_CLAUSE]=2;  //长度为2 
  lit_to_fix[NB_CLAUSE]=NONE;  //预防出错
  replace_clause(NB_CLAUSE, clause1, clauses1); //在clauses1中找到clause1，然后替换成NB_CLAUSE，让var1与clause1脱离关系，与NB_CLAUSE建立关系
  replace_clause(NB_CLAUSE, clause2, clauses2); //在clauses2中找到clause2，然后替换成NB_CLAUSE，让var2与clause2脱离关系，与NB_CLAUSE建立关系
  NB_CLAUSE++; //增加clause个数
}

int verify_binary_clauses(int *varssigns, int var1, int sign1, int var2, int sign2) {  //检测一个什么？ 

  if (var1==*varssigns) {
    if ((*(varssigns+1)!=1-sign1) || (var2!=*(varssigns+2)) ||(*(varssigns+3)!=1-sign2)) {
      printf("problem..");
      return FALSE;
    }
  }
  else {
    if ((var2 != *varssigns) || (*(varssigns+1)!=1-sign2) || (var1!=*(varssigns+2)) || (*(varssigns+3)!=1-sign1)) {
      printf("problem..");
      return FALSE;
    }
  }
  return TRUE;
}

int CLAUSES_TO_REMOVE[tab_clause_size]; //删除的clause?
int CLAUSES_TO_REMOVE_fill_pointer=0;

/*
int create_clause_from_conflict_clauses(int clause1, int clause2, int clause3) { //一个剪枝规则，由冲突的clause来创造clause? 没有发现操作
  int var3, sign3, var2, sign2,*clauses2, *clauses3, *vars_signs,varssigns[4], i=0, var;

  if ((clause_state[clause1]==ACTIVE) && (clause_length[clause1]==2) &&
      (clause_state[clause2]==ACTIVE) && (clause_length[clause2]==1) &&
      (clause_state[clause3]==ACTIVE) && (clause_length[clause3]==1)) {  //条件是clause1,2,3都是active且长度分别为2,1,1
       vars_signs = var_sign[clause1];  // 纪录下clause1中的变量
       for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
           if (var_state[var]==ACTIVE) {   //变量是active的才纪录，由于之前的操作，肯定有两个active的var
               varssigns[i++]=var; varssigns[i++]=*(vars_signs+1);
           }
       }
    var2=varssigns[0]; sign2=1-varssigns[1];
    var3=varssigns[2]; sign3=1-varssigns[3];  //clause1中的正负反过来
    create_binaryclause(var2, sign2, var3, sign3, clause2, clause3);
    _push(clause1, CLAUSES_TO_REMOVE); // 纪录删去哪些clause
    _push(clause2, CLAUSES_TO_REMOVE); // 纪录删去哪些clause
    _push(clause3, CLAUSES_TO_REMOVE); // 纪录删去哪些clause
    return TRUE;
  }
  else {
    return FALSE;  //条件不满足，clause1-3选择有问题 
  }
}*/

int LINEAR_REASON_STACK1[tab_clause_size];
int LINEAR_REASON_STACK1_fill_pointer=0; //栈初始为0的大小
int LINEAR_REASON_STACK2[tab_clause_size];
int LINEAR_REASON_STACK2_fill_pointer=0; //栈初始为0的大小
int clause_involved[tab_clause_size];

int search_linear_reason1(int var) { //搜一个变量
  int *vars_signs, clause, fixed_var, index_var, new_fixed_var;

  for(fixed_var=var; fixed_var!=NONE; fixed_var=new_fixed_var) {
    clause=reason[fixed_var];  //reason来源不明
    vars_signs = var_sign[clause]; 
    new_fixed_var=NONE;
    _push(clause, LINEAR_REASON_STACK1); //纪录下来
    clause_involved[clause]=TRUE; //该clause牵扯其中
    for(index_var=*vars_signs; index_var!=NONE; index_var=*(vars_signs+=2)) {  //扫描该clause中的var
      if ((index_var!=fixed_var) && (reason[index_var]!=NO_REASON)) { //其不等于fixed_var 并且 ？
        if (new_fixed_var==NONE)
            new_fixed_var=index_var;
        else 
            return FALSE;   //如果已经有值了，返回false
      }
    }
  }
  return TRUE;
}

#define SIMPLE_NON_LINEAR_CASE 2

int search_linear_reason2(int var) {
  int *vars_signs, clause, fixed_var, index_var, new_fixed_var;

  for(fixed_var=var; fixed_var!=NONE; fixed_var=new_fixed_var) {
    clause=reason[fixed_var];
    if (clause_involved[clause]==TRUE) {
      if ( LINEAR_REASON_STACK2_fill_pointer == 2 &&
           LINEAR_REASON_STACK1_fill_pointer > 2 &&
           LINEAR_REASON_STACK1[ 2 ] == clause ) 
           return SIMPLE_NON_LINEAR_CASE; //返回这么一种状态，2
      else
           return FALSE;
    }
    else 
      _push(clause, LINEAR_REASON_STACK2);
    vars_signs = var_sign[clause]; new_fixed_var=NONE;  //同search_linear_reason1
    for(index_var=*vars_signs; index_var!=NONE; index_var=*(vars_signs+=2)) {
      if ((index_var!=fixed_var) && (reason[index_var]!=NO_REASON)) {
         if (new_fixed_var==NONE)
           new_fixed_var=index_var;
         else 
           return FALSE;
      }
    }
  }
  return TRUE;
}

// clause1 is l1->l2, clause is l2->l3, clause3 is ((not l3) or (not l4))
// i.e., the reason of l2 is clause1, the reason of l3 is clause
int check_reason(int *varssigns, int clause, int clause1, int clause2) {
  int var, *vars_signs, var1, var2, flag;

  if ((reason[varssigns[0]]!=clause1) || (reason[varssigns[2]]!=clause)) 
    return FALSE;
  vars_signs = var_sign[clause2]; flag=FALSE;
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
    if ((varssigns[2]==var) && (reason[var]!=NO_REASON) && 
  (*(vars_signs+1) != var_current_value[var])) {
      flag=TRUE;
    }
  }
  return flag;
}

int create_complementary_binclause(int clause, int clause1, int clause2) {
  int var, *vars_signs, i=0, varssigns[4], sign, j=0;
  vars_signs = var_sign[clause];
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
    if (reason[var]!=NO_REASON) {
      varssigns[i++]=var; varssigns[i++]=*(vars_signs+1); 
    }
  }
  if (reason[varssigns[2]]==clause1) {
    var=varssigns[2]; sign=varssigns[3];
    varssigns[2]=varssigns[0]; varssigns[3]=varssigns[1];
    varssigns[0]=var; varssigns[1]=sign;
  }
  if ((i!=4) || (check_reason(varssigns, clause, clause1, clause2)==FALSE))
    printf("problem...");
  create_binaryclause(varssigns[0], 1-varssigns[1],
          varssigns[2], 1-varssigns[3], clause1, clause2);
  return TRUE;
}

int get_satisfied_literal(int clause) {  //找该clause中一个var 可以满足这个clause
  int var, *vars_signs;
  vars_signs = var_sign[clause];
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
    if (*(vars_signs+1) == var_current_value[var])
      return var;
  }
  printf("erreur"); //找不到可以满足的
  return NONE;
}

void create_ternary_clauses(int var1, int sign1, int var2, int sign2, 
                            int var3, int sign3, int clause1, 
                            int clause2, int clause3) {      //创建三元clause，同create_binaryclause
  int clause, *vars_signs, *clauses1, *clauses2, *clauses3;
  if (sign1==POSITIVE) clauses1=pos_in[var1]; else clauses1=neg_in[var1];
  if (sign2==POSITIVE) clauses2=pos_in[var2]; else clauses2=neg_in[var2];
  if (sign3==POSITIVE) clauses3=pos_in[var3]; else clauses3=neg_in[var3];
  vars_signs=NEW_CLAUSES[NEW_CLAUSES_fill_pointer++];  //新开一个clause
  vars_signs[0]=var1; vars_signs[1]=sign1;
  vars_signs[2]=var2; vars_signs[3]=sign2;
  vars_signs[4]=var3; vars_signs[5]=sign3;
  vars_signs[6]=NONE;
  var_sign[NB_CLAUSE]=vars_signs;
  clause_state[NB_CLAUSE]=ACTIVE;
  clause_length[NB_CLAUSE]=3;
  replace_clause(NB_CLAUSE, clause1, clauses1);
  replace_clause(NB_CLAUSE, clause2, clauses2);
  replace_clause(NB_CLAUSE, clause3, clauses3);
  NB_CLAUSE++;
}  

int non_linear_conflict(int empty_clause, int var1,int sign1, int var2, int sign2) {
  int var, sign, j;
  // driving unit clause is LINEAR_REASON_STACK1[2] (propagate
  // it resulting the empty_clause by simple non-linear derivation
  // var1, sign1, var2, and sign2 are the two literals of empty_clause
  var=get_satisfied_literal(LINEAR_REASON_STACK1[2]);
  sign=var_current_value[var];
  for(j=2; j<LINEAR_REASON_STACK1_fill_pointer-1; j++) {
    create_complementary_binclause(LINEAR_REASON_STACK1[j],
                                   LINEAR_REASON_STACK1[j+1],
                                   LINEAR_REASON_STACK1[j-1]);
    _push(LINEAR_REASON_STACK1[j], CLAUSES_TO_REMOVE);
  }
  _push(LINEAR_REASON_STACK1[j], CLAUSES_TO_REMOVE);
  create_ternary_clauses(var, sign, var1, sign1, var2, sign2,
                         LINEAR_REASON_STACK1[2],
                         empty_clause, empty_clause);
  create_ternary_clauses(var, 1-sign, var1, 1-sign1, var2, 1-sign2,
                         LINEAR_REASON_STACK2[1],
                         LINEAR_REASON_STACK1[1],
                         LINEAR_REASON_STACK2[1]);
  _push(empty_clause, CLAUSES_TO_REMOVE);
  _push( LINEAR_REASON_STACK1[1], CLAUSES_TO_REMOVE);
  _push( LINEAR_REASON_STACK2[1], CLAUSES_TO_REMOVE);
  return TRUE;
}

  
int linear_conflict(int clause) {
  int var, *vars_signs, i=0, varssigns[6], j=0, res;
  vars_signs = var_sign[clause];
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
    if (reason[var]!=NO_REASON) {
      varssigns[i++]=var; varssigns[i++]=*(vars_signs+1); 
      if (i>4) return FALSE;
    }
  }
  if (i>4) return FALSE;
  if (i==0) printf("bizzar...!!!!!!\n");
  else {
    for(j=0; j<LINEAR_REASON_STACK1_fill_pointer; j++) 
       clause_involved[LINEAR_REASON_STACK1[j]]=NONE;
    LINEAR_REASON_STACK1_fill_pointer=1; LINEAR_REASON_STACK2_fill_pointer=1;
    LINEAR_REASON_STACK1[0]=clause; LINEAR_REASON_STACK2[0]=clause;
    if (search_linear_reason1(varssigns[0])==FALSE)
      return FALSE;
    else {
      if (i==4) {
         res=search_linear_reason2(varssigns[2]);
         if (res==FALSE)
             return FALSE;
         else 
             if (res==SIMPLE_NON_LINEAR_CASE) { 
                 return non_linear_conflict(clause, varssigns[0], varssigns[1], 
                                            varssigns[2], varssigns[3]);
             }
         create_binaryclause(varssigns[0], 1-varssigns[1], 
                             varssigns[2], 1-varssigns[3], 
                             LINEAR_REASON_STACK1[1], LINEAR_REASON_STACK2[1]);
         for(j=1; j<LINEAR_REASON_STACK2_fill_pointer-1; j++) {
           create_complementary_binclause(LINEAR_REASON_STACK2[j],LINEAR_REASON_STACK2[j+1],LINEAR_REASON_STACK2[j-1]);
           _push(LINEAR_REASON_STACK2[j], CLAUSES_TO_REMOVE);
         }
        _push(LINEAR_REASON_STACK2[j], CLAUSES_TO_REMOVE);
      }
      _push(clause, CLAUSES_TO_REMOVE);
      for(j=1; j<LINEAR_REASON_STACK1_fill_pointer-1; j++) {
         create_complementary_binclause(LINEAR_REASON_STACK1[j],
                                        LINEAR_REASON_STACK1[j+1],
                                        LINEAR_REASON_STACK1[j-1]);
         _push(LINEAR_REASON_STACK1[j], CLAUSES_TO_REMOVE);
      }
      _push(LINEAR_REASON_STACK1[j], CLAUSES_TO_REMOVE);
    }
    return TRUE;
  }
  return true;
}

void remove_linear_reasons() {  //两个stack中的拿出来处理
  int i, clause;
  for(i=0; i<LINEAR_REASON_STACK1_fill_pointer; i++) {  
    clause=LINEAR_REASON_STACK1[i];
    clause_state[clause]=PASSIVE;  //关闭掉该cluase 区分passive positive
    _push(clause, CLAUSE_STACK);  //把修改的clause纪录下，放到CLAUSE_STACK中
  }
  for(i=1; i<LINEAR_REASON_STACK2_fill_pointer; i++) { //同上，除了栈不同
    clause=LINEAR_REASON_STACK2[i];
    clause_state[clause]=PASSIVE;
    _push(clause, CLAUSE_STACK); //把修改的clause纪录下，放到CLAUSE_STACK中
  }
}      

int there_is_unit_clause( int var_to_check ) {   //看有没有包涵var_to_check的uniiclause
  int unitclause_position, unitclause, var, *vars_signs;

  for(unitclause_position = 0; unitclause_position < UNITCLAUSE_STACK_fill_pointer; unitclause_position++) { //扫描unitclause
    unitclause = UNITCLAUSE_STACK[ unitclause_position ];  //一个个拿出来看
    if ((clause_state[unitclause] == ACTIVE)  && (clause_length[unitclause]>0)) //是ACTIVE且有长度
      {
        vars_signs = var_sign[unitclause];  //把里面的变量拿出来
        for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) { //看其中的变量
          if ( var == var_to_check && var_state[var] == ACTIVE ) {  //其状态是active且是要找的这个var_to_check
            return TRUE;
          }
        }
      }
  }
  return FALSE;
}

int assign_and_unitclause_process( int var, int value, int starting_point ) {
  int clause;
  var_current_value[var] = value; //把var赋值为value
  var_rest_value[var] = NONE;
  var_state[var] = PASSIVE;  //已经赋值
  _push(var, VARIABLE_STACK); //将其压到栈里去
  if ((clause=my_reduce_clauses_for_fl(var))==NO_CONFLICT) { //不冲突则删除?
    remove_clauses(var);  //把与这个变量相关的clause中都删去这个变量  返回值不管
    return my_unitclause_process( starting_point );
  }
  else {
    return clause;
  }
}

int store_reason_clauses( int clause, int starting ) {
  int *vars_signs, var, i;
  _push(clause, REASON_STACK);
  for(i=starting; i<REASON_STACK_fill_pointer; i++) {
    clause=REASON_STACK[i];
    vars_signs = var_sign[clause];  //把clause中的变量都拿出来看
    for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
      if (reason[var]!=NO_REASON) {
        _push(reason[var], REASON_STACK);
        reason[var]=NO_REASON;
      }
    }
  }
  return i;
}

void remove_reason_clauses() {  //把reason中的clause都拿出来处理
  int i, clause;
  for(i=0; i<REASON_STACK_fill_pointer; i++) {
    clause=REASON_STACK[i];
    clause_state[clause]=PASSIVE;
    _push(clause, CLAUSE_STACK);
  }
  REASON_STACK_fill_pointer=0;
}

int failed_literal( int conflict ) {
  int clause, var, la = 0;
  int saved_clause_stack_fill_pointer, saved_reducedclause_stack_fill_pointer,
    saved_unitclause_stack_fill_pointer, saved_variable_stack_fill_pointer,
    my_saved_clause_stack_fill_pointer, saved_reason_stack_fill_pointer;

  saved_clause_stack_fill_pointer= CLAUSE_STACK_fill_pointer;
  saved_reducedclause_stack_fill_pointer = REDUCEDCLAUSE_STACK_fill_pointer;
  saved_unitclause_stack_fill_pointer = UNITCLAUSE_STACK_fill_pointer;
  saved_variable_stack_fill_pointer=VARIABLE_STACK_fill_pointer; 
  my_saved_clause_stack_fill_pointer= CLAUSE_STACK_fill_pointer;  //把栈顶的大小存起来

  for( var=0; var < NB_VAR && la+conflict+NB_EMPTY<UB; var++ ) {
    if ( var_state[ var ] == ACTIVE &&
         !there_is_unit_clause( var )) {
      simple_get_pos_clause_nb(var); simple_get_neg_clause_nb(var);
      if (nb_neg_clause_of_length2[ var ] > 1 &&  nb_pos_clause_of_length2[ var ] > 1 ) {
      //do {
        if ((clause=assign_and_unitclause_process(var, FALSE, saved_unitclause_stack_fill_pointer))!=NO_CONFLICT) {
    //  printf("One conflict found\n");
          saved_reason_stack_fill_pointer = store_reason_clauses( clause, 0 );
          reset_context(my_saved_clause_stack_fill_pointer,
                        saved_reducedclause_stack_fill_pointer,
                        saved_unitclause_stack_fill_pointer,
                        saved_variable_stack_fill_pointer);  //重置 恢复
          my_saved_clause_stack_fill_pointer=CLAUSE_STACK_fill_pointer;
          if ((clause=assign_and_unitclause_process(var, TRUE, saved_unitclause_stack_fill_pointer))>=0) {
            la++;
            store_reason_clauses( clause, saved_reason_stack_fill_pointer );
            reset_context(my_saved_clause_stack_fill_pointer,
                          saved_reducedclause_stack_fill_pointer,
                          saved_unitclause_stack_fill_pointer,
                          saved_variable_stack_fill_pointer); //重置 恢复
            remove_reason_clauses();
            my_saved_clause_stack_fill_pointer=CLAUSE_STACK_fill_pointer;
         } else {
            REASON_STACK_fill_pointer = 0;
            reset_context(my_saved_clause_stack_fill_pointer,
                          saved_reducedclause_stack_fill_pointer,
                          saved_unitclause_stack_fill_pointer,
                          saved_variable_stack_fill_pointer); //重置 恢复
          }
        } else {
          reset_context(my_saved_clause_stack_fill_pointer,
                        saved_reducedclause_stack_fill_pointer,
                        saved_unitclause_stack_fill_pointer,
                        saved_variable_stack_fill_pointer); //重置 恢复
        }
        //!!There could be more conflicts than just one
        //} while( clause != NO_CONFLICT );
      }
    }
  }
  reset_context(saved_clause_stack_fill_pointer,
                saved_reducedclause_stack_fill_pointer,
                saved_unitclause_stack_fill_pointer,
                saved_variable_stack_fill_pointer); //重置 恢复
  return la;
}
void outputClause(int var){
     int *clauses=pos_in[var]; 
     for (int clause=*clauses;clause!=NONE;clause=*(++clauses)){ 
          if (clause_state[clause]!=ACTIVE) continue; 
          int *vars_signs=var_sign[clause];
          printf("C%d: ",clause);
          for (int var=*vars_signs;var!=NONE;var=*(vars_signs+=2)){
               if (var_state[var]!=ACTIVE) continue;
               if (*(vars_signs+1)==POSITIVE) printf("X%d ",var);
                                         else printf("~X%d ",var);
          }
          puts("");
     } 
     clauses=neg_in[var];
     for (int clause=*clauses;clause!=NONE;clause=*(++clauses)){
          if (clause_state[clause]!=ACTIVE) continue;
          int *vars_signs=var_sign[clause];
          printf("C%d: ",clause);
          for (int var=*vars_signs;var!=NONE;var=*(vars_signs+=2)){
               if (var_state[var]!=ACTIVE) continue;
               if (*(vars_signs+1)==POSITIVE) printf("X%d ",var);
                                         else printf("~X%d ",var);
          }
          puts("");
     }      
}
int lookahead() {
  int saved_clause_stack_fill_pointer, saved_reducedclause_stack_fill_pointer,
      saved_unitclause_stack_fill_pointer, saved_variable_stack_fill_pointer,
      my_saved_clause_stack_fill_pointer,
      clause, conflict=0, var, *vars_signs, i, unitclause;
 
  CLAUSES_TO_REMOVE_fill_pointer=0;
  saved_clause_stack_fill_pointer= CLAUSE_STACK_fill_pointer;
  saved_reducedclause_stack_fill_pointer = REDUCEDCLAUSE_STACK_fill_pointer;
  saved_unitclause_stack_fill_pointer = UNITCLAUSE_STACK_fill_pointer;
  saved_variable_stack_fill_pointer=VARIABLE_STACK_fill_pointer;
  my_saved_clause_stack_fill_pointer= CLAUSE_STACK_fill_pointer;


  while ((clause=my_unitclause_process(0))!=NO_CONFLICT) {
    conflict++;
    if (conflict+NB_EMPTY>=UB) break;
    if (linear_conflict(clause)==TRUE) {
      conflict--; NB_EMPTY++;
      reset_context(my_saved_clause_stack_fill_pointer, 
        saved_reducedclause_stack_fill_pointer,
        saved_unitclause_stack_fill_pointer,
        saved_variable_stack_fill_pointer);  //还原
      remove_linear_reasons();
      my_saved_clause_stack_fill_pointer=CLAUSE_STACK_fill_pointer;
    }
    else 
    {
      _push(clause, REASON_STACK);
      for(i=0; i<REASON_STACK_fill_pointer; i++) {
  clause=REASON_STACK[i]; vars_signs = var_sign[clause];
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
    if (reason[var]!=NO_REASON) {
      _push(reason[var], REASON_STACK);
      reason[var]=NO_REASON;
    }
  }
      }
      reset_context(my_saved_clause_stack_fill_pointer, 
        saved_reducedclause_stack_fill_pointer,
        saved_unitclause_stack_fill_pointer,
        saved_variable_stack_fill_pointer); //还原
      for(i=0; i<REASON_STACK_fill_pointer; i++) {
  clause=REASON_STACK[i];
  clause_state[clause]=PASSIVE; _push(clause, CLAUSE_STACK);
      }
      REASON_STACK_fill_pointer=0;
      my_saved_clause_stack_fill_pointer=CLAUSE_STACK_fill_pointer;
    }
  }
  if ( conflict+NB_EMPTY < UB ) {
    reset_context(my_saved_clause_stack_fill_pointer, 
      saved_reducedclause_stack_fill_pointer,
      saved_unitclause_stack_fill_pointer,
      saved_variable_stack_fill_pointer);  //还原
    conflict += failed_literal( conflict );
  }
    
  reset_context(saved_clause_stack_fill_pointer, 
    saved_reducedclause_stack_fill_pointer,
    saved_unitclause_stack_fill_pointer,
    saved_variable_stack_fill_pointer); 
  if (conflict+NB_EMPTY>=UB) 
    return NONE;



  for (i=0; i<CLAUSES_TO_REMOVE_fill_pointer; i++) {
    clause=CLAUSES_TO_REMOVE[i];
    _push(clause, CLAUSE_STACK); clause_state[clause]=PASSIVE;  //把clause_to_remove中的元素移走
  }
  CLAUSES_TO_REMOVE_fill_pointer=0;
  return conflict;
}

int satisfy_unitclause(int unitclause) {
  int *vars_signs, var, clause;

  vars_signs = var_sign[unitclause];
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) { //扫描这个clause
    if (var_state[var] == ACTIVE ){
      var_current_value[var] = *(vars_signs+1); //值就为在clause中的值
      var_rest_value[var] = NONE;  
      reason[var]=unitclause;
      var_state[var] = PASSIVE;  //状态为已处理
      _push(var, VARIABLE_STACK);
      if ((clause=my_reduce_clauses(var))==NO_CONFLICT) {
             remove_clauses(var);
             return NO_CONFLICT;
      }
      else 
             return clause;
    }
  }
  return NO_CONFLICT;
}
  
int my_unitclause_process(int starting_point) {  // ssign_and_unitclause_process 时用到
  int unitclause, var, *vars_signs, unitclause_position,clause,
    my_unitclause_position, my_unitclause;

  for (unitclause_position = starting_point; 
       unitclause_position < UNITCLAUSE_STACK_fill_pointer;
       unitclause_position++) {
    unitclause = UNITCLAUSE_STACK[unitclause_position];
    if ((clause_state[unitclause] == ACTIVE)  && (clause_length[unitclause]>0)) {
      MY_UNITCLAUSE_STACK_fill_pointer=0;
      if ((clause=satisfy_unitclause(unitclause)) != NO_CONFLICT)
  return clause;
      else {
  for (my_unitclause_position = 0; 
       my_unitclause_position < MY_UNITCLAUSE_STACK_fill_pointer;
       my_unitclause_position++) {
    my_unitclause = MY_UNITCLAUSE_STACK[my_unitclause_position];
    if ((clause_state[my_unitclause] == ACTIVE)  
        && (clause_length[my_unitclause]>0)) {
      if ((clause=satisfy_unitclause(my_unitclause)) != NO_CONFLICT)
        return clause;
    }     
  }
      }
    }
  }
  return NO_CONFLICT;
}

int get_complement(int lit) {
  if (positive(lit)) return lit+NB_VAR; //先判断是正还是反，然后返回其补值(正返回反，反返回正)
  else return lit-NB_VAR;
}

void create_unitclause(int lit, int subsumedclause, int *clauses) { //新加一个unit_clause
  int clause, *vars_signs;

  vars_signs=NEW_CLAUSES[NEW_CLAUSES_fill_pointer++];
  if (lit<NB_VAR) { //看lit的正负
    vars_signs[0]=lit;
    vars_signs[1]=POSITIVE;
  }
  else {
    vars_signs[0]=lit-NB_VAR;
    vars_signs[1]=NEGATIVE;
  }
  vars_signs[2]=NONE;  //标记结束符
  var_sign[NB_CLAUSE]=vars_signs;
  clause_state[NB_CLAUSE]=ACTIVE;
  clause_length[NB_CLAUSE]=1;
  _push(NB_CLAUSE, UNITCLAUSE_STACK); 
  if (!replace_clause(NB_CLAUSE,subsumedclause,clauses)){  
      if (lit>=NB_VAR) lit-=NB_VAR;
      printf("----var:  %d----\n",lit);
      printf("----clause: %d----\n",subsumedclause);
      outputClause(lit);
      outputLit(subsumedclause);
      for (int clause=*clauses;clause!=NONE;clause=*(++clauses))
           if (clause_state[clause]==ACTIVE)
              printf("C%d ",clause);
      puts(""); 
  }
  NB_CLAUSE++; //增加了clause
}

int verify_resolvent(int lit, int clause1, int clause2) {
  int *vars_signs1, *vars_signs2, lit1, lit2, temp, flag=FALSE, var, nb=0;

  if ((clause_state[clause1]!=ACTIVE) || (clause_state[clause2]!=ACTIVE))
      printf("erreur ");
  if ((clause_length[clause1]!=2) || (clause_length[clause2]!=2))
    printf("erreur ");
  vars_signs1=var_sign[clause1];
  vars_signs2=var_sign[clause2];
  for(var=*vars_signs1; var!=NONE; var=*(vars_signs1+=2)) {
    if (var_state[var] == ACTIVE ) {
      nb++;
      if (*(vars_signs1+1)==POSITIVE) 
  temp=var;
      else temp=var+NB_VAR;
      if (temp==lit) flag=TRUE;
      else {
  lit1=temp;
      }
    }
  }
  if ((nb!=2) || (flag==FALSE))
    printf("erreur ");
  nb=0; flag=FALSE;
  for(var=*vars_signs2; var!=NONE; var=*(vars_signs2+=2)) {
    if (var_state[var] == ACTIVE ) {
      nb++;
      if (*(vars_signs2+1)==POSITIVE) 
  temp=var;
      else temp=var+NB_VAR;
      if (temp==lit) flag=TRUE;
      else {
  lit2=temp;
      }
    }
  }
  if ((nb!=2) || (flag==FALSE))
    printf("erreur ");
  if (!complement(lit1, lit2))
    printf("erreur ");
  return 0;
}

int searching_two_clauses_to_fix_neglit(int clause, int lit) {  //lit就是~x
  int lit1, clause1, var1, opp_lit1;
  if (lit_to_fix[clause]==NONE) { //clause去其他的literal无联系
    lit_to_fix[clause]=lit;  //把clause与var联系起来
  }
  else {
    lit1=lit_to_fix[clause]; //该clause与lit1是相关的
    var1=get_var_from_lit(lit1); //得到这个literal对应var的标号
    opp_lit1=get_complement(lit1); //得到相补的值
    clause1=fixing_clause[opp_lit1]; //相补的值所对应的clause
    if ((clause1!= NONE) && (clause_state[clause1]==ACTIVE)) { //这个clause是存在的并且是ACTIVE的
      fixing_clause[opp_lit1]=NONE;
      lit_involved_in_clause[opp_lit1]=NONE;
      _push(clause1, CLAUSE_STACK);
      clause_state[clause1]=PASSIVE; //删除clause1
      _push(clause, CLAUSE_STACK);
      clause_state[clause]=PASSIVE;  //删除clause
      create_unitclause(lit, clause1, neg_in[lit-NB_VAR]); //构造一个unitclause
      var1=get_var_from_lit(lit1);
      nb_neg_clause_of_length2[var1]--;
      nb_pos_clause_of_length2[var1]--;
      return TRUE;
    }
    else {
      fixing_clause[lit1]=clause;
      _push(lit1, CANDIDATE_LITERALS); 
      lit_involved_in_clause[lit1]=clause;
      _push(lit1, INVOLVED_LIT_STACK);
    }
  }
  return FALSE;
}

int simple_get_neg_clause_nb(int var) {
  my_type neg_clause1_nb=0,neg_clause3_nb = 0, neg_clause2_nb = 0;
  int *clauses, clause, i;
  clauses = neg_in[var]; MY_UNITCLAUSE_STACK_fill_pointer=0;

  for(clause=*clauses; clause!=NONE; clause=*(++clauses)) //扫描¬var的所有clause
    if ((clause_state[clause] == ACTIVE) && (clause_length[clause]==2)) //把¬var中的长度为2的a且是ctive的clause找出来
      neg_clause2_nb++;
    nb_neg_clause_of_length2[var] = neg_clause2_nb;
    return neg_clause2_nb;
}

int simple_get_pos_clause_nb(int var) {
  my_type pos_clause1_nb=0,pos_clause3_nb = 0, pos_clause2_nb = 0;
  int *clauses, clause, i;
  clauses = pos_in[var]; MY_UNITCLAUSE_STACK_fill_pointer=0;

  for(clause=*clauses; clause!=NONE; clause=*(++clauses))
    if ((clause_state[clause] == ACTIVE) && (clause_length[clause]==2)) //把var中的长度为2的且是active的clause找出来
      pos_clause2_nb++;
    nb_pos_clause_of_length2[var] = pos_clause2_nb;
    return pos_clause2_nb;
} 
int get_neg_clause_nb(int var) {
  my_type neg_clause1_nb=0,neg_clause3_nb = 0, neg_clause2_nb = 0;
  int *clauses, clause, i;
  clauses = neg_in[var]; MY_UNITCLAUSE_STACK_fill_pointer=0;

  for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {  //扫描包涵var反的各个clause
    if ((clause_state[clause] == ACTIVE) && (clause_length[clause]>0)) {  //要这个clause为active的且长度大于0 
      switch(clause_length[clause]) {
      case 1: neg_clause1_nb++;           //长度为1
              _push(clause, MY_UNITCLAUSE_STACK); break; //把其记到MY_UNITCLAUSE_STACK中
      case 2: neg_clause2_nb++;          //长度为2
              if (searching_two_clauses_to_fix_neglit(clause, var+NB_VAR)==TRUE) {  //带进去的var是～的
                   neg_clause2_nb-=2; neg_clause1_nb++; 
              }
              break; 
      default: neg_clause3_nb++; break;  //长度>=3
      }
    }
  }
  for(i=0; i<CANDIDATE_LITERALS_fill_pointer; i++)  //candidate是干嘛的
    fixing_clause[CANDIDATE_LITERALS[i]]=NONE;   //fix是干嘛的
  CANDIDATE_LITERALS_fill_pointer=0;
  nb_neg_clause_of_length1[var] = neg_clause1_nb;
  nb_neg_clause_of_length2[var] = neg_clause2_nb;
  nb_neg_clause_of_length3[var] = neg_clause3_nb;  //纪录一下三者个数 
  return neg_clause1_nb+neg_clause2_nb + neg_clause3_nb; //返回三者之和
}

#define OTHER_LIT_FIXED 1
#define THIS_LIT_FIXED 2

int searching_two_clauses_to_fix_poslit(int clause, int lit) {   //lit就是x
  int lit1, clause1, var1, opp_lit1;
  if (lit_to_fix[clause]==NONE) { 
    lit_to_fix[clause]=lit;
  }
  else {
    lit1=lit_to_fix[clause];
    var1=get_var_from_lit(lit1);
    clause1=lit_involved_in_clause[lit1];
    if ((clause1!=NONE) && (clause_state[clause1]==ACTIVE)) {
      //  verify_resolvent(lit1, clause1, clause);
      _push(clause1, CLAUSE_STACK);
      clause_state[clause1]=PASSIVE;
      _push(clause, CLAUSE_STACK);
      clause_state[clause]=PASSIVE;
      if (lit1<NB_VAR) { //为正  
           create_unitclause(lit1, clause1, pos_in[lit1]);
           nb_pos_clause_of_length2[lit1]-=2;
           nb_pos_clause_of_length1[lit1]++;
      }
      else {  //为负 
           create_unitclause(lit1, clause1, neg_in[lit1-NB_VAR]);
           nb_neg_clause_of_length2[lit1-NB_VAR]-=2;
           nb_neg_clause_of_length1[lit1-NB_VAR]++;
      }
      return OTHER_LIT_FIXED; //返回1
    }
    else {
      opp_lit1=get_complement(lit1);
      clause1=fixing_clause[opp_lit1];
      if ((clause1!= NONE) && (clause_state[clause1]==ACTIVE)) {
         fixing_clause[opp_lit1]=NONE;
         // verify_resolvent(lit, clause1, clause);
         _push(clause1, CLAUSE_STACK);
         clause_state[clause1]=PASSIVE;
         _push(clause, CLAUSE_STACK);
         clause_state[clause]=PASSIVE;  
         create_unitclause(lit, clause1, pos_in[lit]);
         var1=get_var_from_lit(lit1);
         nb_neg_clause_of_length2[var1]--;
         nb_pos_clause_of_length2[var1]--;
         return THIS_LIT_FIXED;
      }
      else {
         fixing_clause[lit1]=clause; //包含lit1的2-clause
         _push(lit1, CANDIDATE_LITERALS);
      }
    }
  }
  return FALSE;
}

int get_pos_clause_nb(int var) {
  my_type pos_clause1_nb=0, pos_clause3_nb = 0, pos_clause2_nb = 0; //清零
  int *clauses, clause, clause1, i;
  clauses = pos_in[var];
  for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if ((clause_state[clause] == ACTIVE) && (clause_length[clause]>0)) { 
      switch(clause_length[clause]) {
      case 1:
  if (MY_UNITCLAUSE_STACK_fill_pointer>0) {
    clause1=_pop(MY_UNITCLAUSE_STACK);
    clause_state[clause]=PASSIVE;
    _push(clause, CLAUSE_STACK);
    clause_state[clause1]=PASSIVE;
    _push(clause1, CLAUSE_STACK);
    nb_neg_clause_of_length1[var]--;
    NB_EMPTY++;
  }
  else pos_clause1_nb++; 
  break;
      case 2: pos_clause2_nb++; 
  switch(searching_two_clauses_to_fix_poslit(clause, var)) {
  case OTHER_LIT_FIXED: nb_neg_clause_of_length2[var]--;
    pos_clause2_nb--;
    break;
  case THIS_LIT_FIXED: pos_clause2_nb-=2;
    pos_clause1_nb++;
    break;
  }
  break;
      default: pos_clause3_nb++; break;
      }
    }
  }
  for(i=0; i<CANDIDATE_LITERALS_fill_pointer; i++) 
    fixing_clause[CANDIDATE_LITERALS[i]]=NONE;
  CANDIDATE_LITERALS_fill_pointer=0;
  for(i=0; i<INVOLVED_LIT_STACK_fill_pointer; i++) 
    lit_involved_in_clause[INVOLVED_LIT_STACK[i]]=NONE;
  INVOLVED_LIT_STACK_fill_pointer=0;
  nb_pos_clause_of_length1[var] = pos_clause1_nb;
  nb_pos_clause_of_length2[var] = pos_clause2_nb;
  nb_pos_clause_of_length3[var] = pos_clause3_nb; 
  return pos_clause1_nb+pos_clause2_nb + pos_clause3_nb;
}

int satisfy_literal(int lit) {
  int var;
  if (positive(lit)) {  //这个变量是正的
    if (var_state[lit]==ACTIVE) {
      var_current_value[lit] = TRUE;
      if (reduce_clauses(lit)==FALSE) return NONE;
      var_rest_value[lit]=NONE;
      var_state[lit] = PASSIVE;
      _push(lit, VARIABLE_STACK);
      remove_clauses(lit);
    }
    else
      if (var_current_value[lit]==FALSE) return NONE;
  } 
  else {
    var = get_var_from_lit(lit);
    if (var_state[var]==ACTIVE) {
      var_current_value[var] = FALSE;
      if (reduce_clauses(var)==FALSE) return NONE;
      var_rest_value[var]=NONE;
      var_state[var] = PASSIVE;
      _push(var, VARIABLE_STACK);
      remove_clauses(var);
    }
    else
      if (var_current_value[var]==TRUE) return NONE;
  }
  return TRUE;
}

int assign_value(int var, int current_value, int rest_value) {  //给var赋值， rest的意思是？
  if (var_state[var]!=ACTIVE)
    printf("erreur1...\n");
  var_state[var] = PASSIVE;
  _push(var, VARIABLE_STACK);
  var_current_value[var] = current_value; //给一个赋值
  var_rest_value[var] = rest_value;
  if (reduce_clauses(var)==NONE)   //注意区分redue与remove,reduce是去除clause中的该变量，也就是其赋值在这个clause中为0
    return NONE;
  remove_clauses(var);    //remove是移除var赋值后可满足的clause
  return TRUE;
}
 
int unitclause_process() {  //处理unit_clause
  int unitclause, var, *vars_signs, unitclause_position,clause;
  for (unitclause_position = 0; unitclause_position < UNITCLAUSE_STACK_fill_pointer; unitclause_position++) {
    unitclause = UNITCLAUSE_STACK[unitclause_position];  //扫描之前纪录的unit_clause
    if ((clause_state[unitclause] == ACTIVE)  && (clause_length[unitclause]>0)) { //是active的且长度大于0
      vars_signs = var_sign[unitclause];
      for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) { //看其一个个变量
         if (var_state[var] == ACTIVE ){   //变量要是active的，则找到了这个变量
             var_current_value[var] = *(vars_signs+1);  //按照原来的正负来赋值
             var_rest_value[var] = NONE;  //之前的赋值？
             var_state[var] = PASSIVE;  //变为非active
             _push(var, VARIABLE_STACK);  //记住变了哪些变量
             if ((clause=reduce_clauses(var)) !=NONE) { //把var在出现的clause中抹除  为NONE则说明被upperbound限制住了
               remove_clauses(var);
               break;
             }
             else {
               return NONE;
             }
          }
        }
    }     
  }
  return TRUE; //没有被upper bound限制住
}
bool c1c2[tab_variable_size][2];
bool judgeClauseAndVar(){
   for (int clause=0; clause<NB_CLAUSE; clause++){
      if (clause_state[clause]!=ACTIVE) continue;
      int *vars_signs=var_sign[clause];
      for (int lit=*vars_signs;lit!=NONE;lit=*(vars_signs+=2)){
           if (var_state[lit]!=ACTIVE) continue;
           int *clauses,c;
           if (*(vars_signs+1)==POSITIVE) clauses=pos_in[lit];
                                     else clauses=neg_in[lit];
           for (c=*clauses;c!=NONE;c=*(++clauses))
               if (c==clause) break;
           if (c==NONE){
              printf("Clause: %d  var: %d\n",clause,lit);
              return false;     
           }                    
      }
  }  
  return true;
}  
//--------------rule 3-----------------
map<int,int> temp_clause; 
void sort_clause(int clause){
  int *vars=var_sign[clause];
  for (int i=0;vars[i]!=NONE;i+=2)
    for (int j=i+2;vars[j]!=NONE;j+=2)
      if (vars[i]>vars[j]){
          swap(vars[i],vars[j]);
          swap(vars[i+1],vars[j+1]);
      }
}
void outputLit(int c){
  int *vars_signs=var_sign[c];
  for (int var=*vars_signs;var!=NONE;var=*(vars_signs+=2)){
      if (var_state[var]!=ACTIVE) continue;
      //printf("%d ",var);
      if (*(vars_signs+1)==POSITIVE) printf("X%d ",var);
                              else  printf("~X%d ",var);
  }
  puts("");
  //puts("\n--------------------------");
}
int length_of_clause(int c){
  int *vars_signs=var_sign[c],nb=0;
  for (int var=0;var!=NONE;var=*(vars_signs+=2))
      if (var_state[var]==ACTIVE) nb++;
  return nb;
}
int rule3num=0;
bool rule3(int var){
  if (!DEBUG_OPEN_RULE3) return false;  
  int c1=-1,c2=-1,*clauses=pos_in[var]; 
  for(int clause=*clauses; clause!=NONE; clause=*(++clauses)) 
     if (clause_state[clause] == ACTIVE){
          if (c1==-1) c1=clause;
                 else return false;
     }  
  if (c1==-1) return false; //包含var的是否有且仅有一个clause 

  clauses=neg_in[var];
  for(int clause=*clauses; clause!=NONE; clause=*(++clauses)) 
     if (clause_state[clause] == ACTIVE){
          if (c2==-1) c2=clause;
                 else return false;
     }  
  if (c2==-1) return false; //包含~var的是否有且仅有一个clause      
  //往下走都是return true
  int *c,*vars_signs; 
  vars_signs=var_sign[c2];
  //-----------------构造递推关系
  recur[var].clear(); 
  for (int lit=*vars_signs;lit!=NONE;lit=*(vars_signs+=2)){
      if (var_state[lit]!=ACTIVE) continue;
      if (lit==var) continue;
      if (*(vars_signs+1)==POSITIVE) recur[var].insert(lit);
                                else recur[var].insert(lit+NB_VAR);
  } 
  //-----------------构造递推关系
  _push(var, VARIABLE_STACK); 
  var_state[var] = DONE;   //需要通过递推确定值
  var_rest_value[var] = POSITIVE; //随意赋值
  var_rest_value[var] = NONE;
  _push(c1, CLAUSE_STACK); clause_state[c1]=PASSIVE;  //删去c1
  _push(c2, CLAUSE_STACK); clause_state[c2]=PASSIVE;  //删去c2
  temp_clause.clear();
  vars_signs=var_sign[c1]; 
  for (int lit=*vars_signs;lit!=NONE;lit=*(vars_signs+=2)){
      if (var_state[lit]!=ACTIVE) continue;
      if (*(vars_signs+1)==POSITIVE) temp_clause[lit]=c1; //0~NB_VAR-1 为正
                                else temp_clause[lit+NB_VAR]=c1;   //为~lit
  }
  vars_signs=var_sign[c2];
  for (int lit=*vars_signs;lit!=NONE;lit=*(vars_signs+=2)){
      if (var_state[lit]!=ACTIVE) continue;
      if (*(vars_signs+1)==POSITIVE) temp_clause[lit]=c2;
                                else temp_clause[lit+NB_VAR]=c2; 
  } 

  int *new_var_signs=NEW_CLAUSES[NEW_CLAUSES_fill_pointer++]; //新分配一个clause 
  int nb=0;
  map<int,int>::iterator it3;
  var_sign[NB_CLAUSE]=new_var_signs; //注意  

  for (it3=temp_clause.begin();it3!=temp_clause.end();it3++){
      int lit=it3->first,c=it3->second;
      nb++; 
      if (lit<NB_VAR){  //为正
        *(new_var_signs++)=lit; 
        *(new_var_signs++)=POSITIVE;
        replace_clause(NB_CLAUSE,c,pos_in[lit]);
      }else{
        lit-=NB_VAR; 
        *(new_var_signs++)=lit; 
        *(new_var_signs++)=NEGATIVE; 
        replace_clause(NB_CLAUSE,c,neg_in[lit]);
      }
  }
  *(new_var_signs)=NONE;
  clause_state[NB_CLAUSE]=ACTIVE; 
  clause_length[NB_CLAUSE]=nb;   
  lit_to_fix[NB_CLAUSE]=NONE; //注意此处需要清空
  sort_clause(NB_CLAUSE);     
  NB_CLAUSE++; 
  return true; 
}
//--------------rule 3-----------------
//-------------------------------rule 6--------------------------------- 
int nb_var_clause[2]; //0负，1正 
void update_nb_of_var_clause(int var){
    nb_var_clause[0]=nb_var_clause[1]=0; 
    int *clauses=pos_in[var];
    for (int clause=*clauses;clause!=NONE;clause=*(++clauses))  //修正bug
        if (clause_state[clause]==ACTIVE) nb_var_clause[1]++;
    
    clauses=neg_in[var];
     for (int clause=*clauses;clause!=NONE;clause=*(++clauses))
        if (clause_state[clause]==ACTIVE) nb_var_clause[0]++;   
}
int findASingleton(int *clauses){ 
     int D=-1;
     for (int clause=*clauses;clause!=NONE;clause=*(++clauses))
         if (clause_state[clause]==ACTIVE){
            if (D==-1) D=clause;
                  else return -1;
         } 
     return D; 
}
//----valid的变量才进入操作----
int rule6num=0;
int had[tab_variable_size][2]; //0负，1正
int new_var[tab_variable_size][2]; //纪录新加的clause中包含哪些lit
int unitnum[tab_variable_size][2]; 
void rule6_2_clean_clause(int clause){
  int *vars_signs=var_sign[clause],var,sign;
  for (var=*vars_signs;var!=NONE;var=*(vars_signs+=2)){
      if (var_state[var]!=ACTIVE) continue;
      sign=*(vars_signs+1);
      if (sign==POSITIVE) nb_pos_clause_of_length3[var]--;
                     else nb_neg_clause_of_length3[var]--; 
  }
}
bool run_rule_6_1(int var0,int *a,int *b,int sign0){
  int D=findASingleton(a),num;  
  bool flagRule6=false,flagRule6_1;
  if (D==-1) return false; 
  int *vars_signs0=var_sign[D];
  memset(had,false,sizeof(had));
  for (int var1=*(vars_signs0);var1!=NONE;var1=*(vars_signs0+=2)){
      if (var_state[var1]!=ACTIVE) continue;
      if (var1==var0) continue;
      had[var1][*(vars_signs0+1)]=true; 
  }  
  int *clauses=b; //i个clause一个个看
  for (int clause=*clauses;clause!=NONE;clause=*(++clauses)){  //扫描i个clause
      if (clause_state[clause]!=ACTIVE) continue;
      vars_signs0=var_sign[clause];
      flagRule6_1=false;
      num=0;
      for (int var1=*vars_signs0;var1!=NONE;var1=*(vars_signs0+=2)){
        if (var_state[var1]!=ACTIVE) continue;
        int sign=*(vars_signs0+1);
        if (had[var1][sign]){
            flagRule6_1=true; //可以做rule6.1
            continue;
        }
        new_var[num][0]=var1;
        new_var[num][1]=sign;
        num++;
      }
      if (!flagRule6_1) continue;  //能否执行rule6.1
      //-----------run_rule_6_1-------------
      int *new_var_signs=NEW_CLAUSES[NEW_CLAUSES_fill_pointer++]; //新分配一个clause
      int nb=0,*c;
      var_sign[NB_CLAUSE]=new_var_signs; //注意
      for (int index=0;index<num;index++){ 
          int lit=new_var[index][0],sign=new_var[index][1];
          *(new_var_signs++)=lit;
          *(new_var_signs++)=sign;
          nb++;
          if (sign==POSITIVE) c=pos_in[lit];
                         else c=neg_in[lit];
          replace_clause(NB_CLAUSE, clause, c);  
      }
      *(new_var_signs)=NONE;
      clause_state[NB_CLAUSE]=ACTIVE; 
      clause_length[NB_CLAUSE]=nb; 
      lit_to_fix[NB_CLAUSE]=NONE;
      sort_clause(NB_CLAUSE);
      _push(clause, CLAUSE_STACK); clause_state[clause]=PASSIVE;  
      NB_CLAUSE++;    
      rule6num++;      
      flagRule6=true;
  }
  return flagRule6;
}
int store_rule_6_2[tab_clause_size][3];
bool run_rule_6_2(int var0,int *a,int *b,int sign0){
  int D=findASingleton(a),num,iNum,*clauses;  
  bool flagRule6=false;
  if (D==-1) return false;
  clauses=b,iNum=0;  //iNum纪录其(i,1)  (1,i)中i的大小
  for (int clause=*clauses;clause!=NONE;clause=*(++clauses))
      if (clause_state[clause]==ACTIVE) iNum++; 
  num=0; //可以做rule6_2规则的个数
  int *vars_signs0=var_sign[D];
  memset(had,false,sizeof(had));
  for (int var1=*(vars_signs0);var1!=NONE;var1=*(vars_signs0+=2)){
      if (var_state[var1]!=ACTIVE) continue;
      if (var1==var0) continue;
      had[var1][*(vars_signs0+1)]=true; 
  }  
  clauses=b; //i个clause一个个看
  for (int clause=*clauses;clause!=NONE;clause=*(++clauses)){  //扫描i个clause
      if (clause_state[clause]!=ACTIVE) continue;
      vars_signs0=var_sign[clause];  
      for (int var1=*vars_signs0;var1!=NONE;var1=*(vars_signs0+=2)){
          if (var_state[var1]!=ACTIVE) continue;
          int sign=*(vars_signs0+1);
          if (had[var1][1-sign]){ //进入rule6.2
            //-----新添加的-------
            flagRule6=true;
            if (num>0 && store_rule_6_2[num][0]!=clause){
                num++;
                store_rule_6_2[num][0]=clause;
                store_rule_6_2[num][1]=var1,store_rule_6_2[num][2]=sign;
                if (num==iNum-1){
                   for (int i=1;i<iNum;i++){ //把这i-1个clause删去...留下最后一个来做rule3
                      clause=store_rule_6_2[i][0];
                      _push(clause,CLAUSE_STACK), clause_state[clause]=PASSIVE;
                   }
                   rule3(var0);
                   return true;
                }
            }
            //------------------
        } 
      }
  } 
  return false;
  for (int index=1;index<=num;index++){  //那就拿出来一个个处理
    int clause=store_rule_6_2[index][0],var1=store_rule_6_2[index][1],sign=store_rule_6_2[index][2];
    if (nb_var_clause[1-sign0]==2){  //原rule5  若i为2  直接删去该clause 
        _push(clause,CLAUSE_STACK), clause_state[clause]=PASSIVE;
        nb_var_clause[1-sign0]=1; 
        rule6num++;  
    }else
    if (length_of_clause(clause)>2){  //原rule5的规则,若clause长度为2则只保留x y 
      if (unitnum[var1][1-sign]){  //剩下只有x,y的two-clause,所以可以尝试进入
        unitnum[var1][1-sign]--;
        assign_value(var0,1-sign0,NONE);   
        return true;
      }
      create_binaryclause(var0,1-sign0,var1,sign,clause,clause); //只保留xy
      rule6_2_clean_clause(clause);
      if (sign0==POSITIVE) nb_neg_clause_of_length2[var0]++; 
                     else  nb_pos_clause_of_length2[var0]++; 
      if (sign==POSITIVE)  nb_pos_clause_of_length2[var1]++; 
                     else  nb_neg_clause_of_length2[var1]++;       
      _push(clause,CLAUSE_STACK), clause_state[clause]=PASSIVE; //删除原clause 
      rule6num++;  
    }
  }
  return flagRule6;
}
bool rule6(int var0){    
  update_nb_of_var_clause(var0);  
  memset(unitnum,0,sizeof(unitnum)); //纪录每个变量的unit-clause个数
  for (int index=0;index<UNITCLAUSE_STACK_fill_pointer;index++){
     int clause=UNITCLAUSE_STACK[index];
     if (clause_state[clause]==ACTIVE){
         int *vars_signs=var_sign[clause];
         for (int var=*vars_signs;var!=NONE;var=*(vars_signs+=2))
            if (var_state[var]==ACTIVE)
               unitnum[var][*(vars_signs+1)]++; 
     }
   }  
  if (run_rule_6_1(var0,pos_in[var0],neg_in[var0],POSITIVE)) return true;  // x (1,i)
  if (run_rule_6_1(var0,neg_in[var0],pos_in[var0],NEGATIVE)) return true;  // x (i,1)
  if (run_rule_6_2(var0,pos_in[var0],neg_in[var0],POSITIVE)) return true;  // x (1,i)
  if (run_rule_6_2(var0,neg_in[var0],pos_in[var0],NEGATIVE)) return true;  // x (i,1)
  return false;
}
//-------------------------------rule 6--------------------------------- 
//-------------------------------rule 7-----------------------------------
//要加入x'如何操作
void rule7(int var0){
    update_nb_of_var_clause(var0); 
    memset(had,0,sizeof(had));
    if (nb_var_clause[1]==1){  // x为(1,i)
       int D=findASingleton(pos_in[var0]),num=0;
       int *clauses=neg_in[var0];
       for (int clause=*clauses;clause!=NONE;clause=*(++clauses)){
            if (clause_state[clause]!=ACTIVE) continue;
            num++;
            int *vars_signs=var_sign[clause];
            for (int var1=*vars_signs;var1!=NONE;var1=*(vars_signs+=2)){
                 if (var_state[var1]!=ACTIVE) continue;
                 had[var1][*(vars_signs+1)]++;
            }
       }    
       int var1=-1,sign;
       for (var1=0; var1<NB_VAR; var1++)
          for (sign=0;sign<2;sign++)
            if (had[var1][sign]==num)
              break;
       
  } 
  memset(had,0,sizeof(had));
  if (nb_var_clause[0]==1){  // x为(i,1)
       int D=findASingleton(neg_in[var0]),num=0;
       int *clauses=pos_in[var0];
       for (int clause=*clauses;clause!=NONE;clause=*(++clauses)){
            if (clause_state[clause]!=ACTIVE) continue;
            num++;
            int *vars_signs=var_sign[clause];
            for (int var1=*vars_signs;var1!=NONE;var1=*(vars_signs+=2)){
                 if (var_state[var1]!=ACTIVE) continue;
                 had[var1][*(vars_signs+1)]++;
            }
       }    
       int var1=-1,sign;
       for (var1=0; var1<NB_VAR; var1++)
          for (sign=0;sign<2;sign++)
            if (had[var1][sign]==num)
              break;
        
  }
}
//-------------------------------rule 7-----------------------------------
//-------------------------------rule 4-----------------------------------
void create_new_clause(){
  int *new_var_signs=NEW_CLAUSES[NEW_CLAUSES_fill_pointer++]; //新分配一个clause 
  int nb=0;
  map<int,int>::iterator it3;
  var_sign[NB_CLAUSE]=new_var_signs; //注意  
  for (it3=temp_clause.begin();it3!=temp_clause.end();it3++){
      int lit=it3->first,c=it3->second;
      nb++; 
      if (lit<NB_VAR){  //为正
        *(new_var_signs++)=lit; 
        *(new_var_signs++)=POSITIVE;
        replace_clause(NB_CLAUSE,c,pos_in[lit]);
      }else{
        lit-=NB_VAR; 
        *(new_var_signs++)=lit; 
        *(new_var_signs++)=NEGATIVE;  
        replace_clause(NB_CLAUSE,c,neg_in[lit]);
      }
  }
  *(new_var_signs)=NONE;
  clause_state[NB_CLAUSE]=ACTIVE; 
  clause_length[NB_CLAUSE]=nb;   
  lit_to_fix[NB_CLAUSE]=NONE; //注意此处需要清空
  sort_clause(NB_CLAUSE);    
  NB_CLAUSE++; 
}
bool run_rule4(int var0,int *a,int *b){
  int D=findASingleton(b);  //找到singleton  
  if (length_of_clause(D)>MAX_N_SAT) return false;  
  int *clauses0=a,c0=-1,c1=-1;  //c0是xy的
  for (int clause=*clauses0;clause!=NONE;clause=*(++clauses0)){
      if (clause_state[clause]!=ACTIVE) continue;
      if (c0==-1) c0=clause;
             else c1=clause; 
  }
  if (length_of_clause(c1)==2) swap(c0,c1);
  if (length_of_clause(c0)!=2 || length_of_clause(D)<2) return false;     
  int var1,sign,*vars_signs=var_sign[c0];
  for (var1=*vars_signs;var1!=NONE;var1=*(vars_signs+=2)) //找到y
      if (var_state[var1]==ACTIVE && var1!=var0){
          sign=*(vars_signs+1);
          break;
      }  

  _push(var0, VARIABLE_STACK); 
  var_state[var0] = DONE;   //需要通过递推确定值 
  var_rest_value[var0] = POSITIVE; //随意赋值
  var_rest_value[var0] = NONE;
  _push(c0,CLAUSE_STACK), clause_state[c0]=PASSIVE;
  _push(c1,CLAUSE_STACK), clause_state[c1]=PASSIVE;
  _push(D,CLAUSE_STACK),  clause_state[D]=PASSIVE;   //删去c0,c1,D

  temp_clause.clear();
  if (sign==POSITIVE) temp_clause[var1]=c0;      //先将y放入
                 else temp_clause[var1+NB_VAR]=c0;
  vars_signs=var_sign[D];
  for (int var=*vars_signs;var!=NONE;var=*(vars_signs+=2)){
     if (var_state[var]!=ACTIVE) continue;
     if (*(vars_signs+1)==POSITIVE) temp_clause[var]=D;
                               else temp_clause[var+NB_VAR]=D;
  } 
  create_new_clause();  

  temp_clause.clear();
  if (sign==NEGATIVE) temp_clause[var1]=NONE;  //将~y放入
                 else temp_clause[var1+NB_VAR]=NONE; 
  vars_signs=var_sign[c1];
  for (int var=*vars_signs;var!=NONE;var=*(vars_signs+=2)){
      if (var_state[var]!=ACTIVE) continue;
      if (*(vars_signs+1)==POSITIVE) temp_clause[var]=c1;
                                else temp_clause[var+NB_VAR]=c1;
  } 
  vars_signs=var_sign[D];

  for (int var=*vars_signs;var!=NONE;var=*(vars_signs+=2)){
      if (var_state[var]!=ACTIVE) continue; 
      if (*(vars_signs+1)==POSITIVE) temp_clause[var]=D;
                                else temp_clause[var+NB_VAR]=D;
  }  

  create_new_clause();
  return true;
}
bool run_rule4_2(int var0,int *a,int *b){
  int Cy=-1,Cz=-1,C1=-1,D=findASingleton(b);
  int *clauses=a;
  for (int clause=*clauses;clause!=NONE;clause=*(++clauses)){
      if (clause_state[clause]!=ACTIVE) continue;
      if (Cy==-1) Cy=clause; else
      if (Cz==-1) Cz=clause; else
                  C1=clause;
  }
  if (length_of_clause(Cy)!=2) swap(Cy,C1);
  if (length_of_clause(Cz)!=2) swap(Cz,C1);
  if (length_of_clause(D)<2 || length_of_clause(Cy)!=2 || length_of_clause(Cz)!=2) return false;
  int y,z,signy,signz,*vars_signs;
  vars_signs=var_sign[Cy];
  for (y=*vars_signs;y!=var0 && var_state[y]!=ACTIVE;y=*(vars_signs+=2));
  signy=*(vars_signs+1);
  vars_signs=var_sign[Cz];
  for (z=*vars_signs;y!=var0 && var_state[z]!=ACTIVE;z=*(vars_signs+=2));
  signz=*(vars_signs+1);

  _push(var0, VARIABLE_STACK); 
  var_state[var0] = DONE;   //需要通过递推确定值
  //-----------------构造递推关系
  recur[var0].clear();  //x= ~y ~z
  if (signy==POSITIVE) recur[var0].insert(y+NB_VAR);
                  else recur[var0].insert(y);
  if (signz==POSITIVE) recur[var0].insert(z+NB_VAR);
                  else recur[var0].insert(z);
  //-----------------构造递推关系
  var_rest_value[var0] = POSITIVE; //随意赋值
  var_rest_value[var0] = NONE;
  _push(Cy,CLAUSE_STACK), clause_state[Cy]=PASSIVE;
  _push(Cz,CLAUSE_STACK), clause_state[Cz]=PASSIVE;
  _push(C1,CLAUSE_STACK), clause_state[C1]=PASSIVE;
  _push(D,CLAUSE_STACK),  clause_state[D]=PASSIVE;   //删去Cz,Cy,C1,D

  temp_clause.clear();
  if (signy==POSITIVE) temp_clause[y]=Cy;      //先将y放入
                  else temp_clause[y+NB_VAR]=Cy;
  vars_signs=var_sign[D];
  for (int var=*vars_signs;var!=NONE;var=*(vars_signs+=2)){
     if (var_state[var]!=ACTIVE) continue;
     if (*(vars_signs+1)==POSITIVE) temp_clause[var]=D;
                               else temp_clause[var+NB_VAR]=D;//将D中的元素放入
  } 
  create_new_clause();    //新建yD

  temp_clause.clear();
  if (signy==NEGATIVE) temp_clause[y]=NONE;  //将~y放入
                  else temp_clause[y+NB_VAR]=NONE;  
  if (signz==POSITIVE) temp_clause[z]=Cz;      //将z放入
                  else temp_clause[z+NB_VAR]=Cz;                
  vars_signs=var_sign[D];
  for (int var=*vars_signs;var!=NONE;var=*(vars_signs+=2)){
     if (var_state[var]!=ACTIVE) continue;
     if (*(vars_signs+1)==POSITIVE) temp_clause[var]=D;
                               else temp_clause[var+NB_VAR]=D; //将D中的元素放入
  }   
  create_new_clause(); //新建~y,z,D

  temp_clause.clear();
  if (signy==NEGATIVE) temp_clause[y]=NONE;  //将~y放入
                  else temp_clause[y+NB_VAR]=NONE;  
  if (signz==NEGATIVE) temp_clause[z]=NONE;  //将~z放入
                  else temp_clause[z+NB_VAR]=NONE;  
  vars_signs=var_sign[C1];
  for (int var=*vars_signs;var!=NONE;var=*(vars_signs+=2)){
     if (var_state[var]!=ACTIVE) continue;
     if (*(vars_signs+1)==POSITIVE) temp_clause[var]=C1; 
                               else temp_clause[var+NB_VAR]=C1; //将C1中的元素放入
  } 
  vars_signs=var_sign[D];
  for (int var=*vars_signs;var!=NONE;var=*(vars_signs+=2)){
     if (var_state[var]!=ACTIVE) continue;
     if (*(vars_signs+1)==POSITIVE) temp_clause[var]=D;
                               else temp_clause[var+NB_VAR]=D; //将D中的元素放入
  }    
  create_new_clause(); //新建~y,~z,C1,D

  return true;
}
int rule4num=0;
bool rule4(int var0){
  if (!DEBUG_OPEN_RULE4) return false;
  update_nb_of_var_clause(var0);    
  if (nb_var_clause[1]==2 && nb_var_clause[0]==1) //x为(2,1)
    if (run_rule4(var0,pos_in[var0],neg_in[var0])) { 
      return true;
    }  
  if (nb_var_clause[0]==2 && nb_var_clause[1]==1) //x为(1,2)
    if (run_rule4(var0,neg_in[var0],pos_in[var0])) {  
      return true;
    }   
  if (nb_var_clause[1]==3 && nb_var_clause[0]==1) //x为(3,1)
    if (run_rule4_2(var0,pos_in[var0],neg_in[var0])){  
      return true;
    }
  if (nb_var_clause[0]==3 && nb_var_clause[1]==1) //x为(1,3)
    if (run_rule4_2(var0,neg_in[var0],pos_in[var0])){  
      return true;
    } 
  return false;
}
//-------------------------------rule 4----------------------------------- 
int rule2num=0; 
int choose_and_instantiate_variable() {  //所有的var赋值操作都在其中
  int var, nb=0, chosen_var=NONE,cont=0, cont1;  
  int a,b,c,clause;
  float poid, max_poid = -1.0; 
  bool run_rule2=true;
  my_type pos2, neg2, flag=0;
  NB_BRANCHE++;    //统计分支个数 
  A: ;
  if (run_rule2==true){
    run_rule2=false;
  if (lookahead()==NONE)
    return NONE;

  if (UB-NB_EMPTY==1)
    if (unitclause_process() ==NONE) //处理了unitclause后可以被upper bound限制住 返回
      return NONE;
 
  for (clause=0; clause<NB_CLAUSE; clause++) 
    lit_to_fix[clause]=NONE;  //将其都清空   
   
  for (var = 0; var < NB_VAR; var++) {
    if (var_state[var] == ACTIVE) { 

      reduce_if_negative[var]=0; //纪录将var取正与取负的影响
      reduce_if_positive[var]=0;

      if (get_neg_clause_nb(var) == 0) {
         NB_MONO++;
         var_current_value[var] = TRUE;
         var_rest_value[var] = NONE;
         var_state[var] = PASSIVE;
         _push(var, VARIABLE_STACK);
         remove_clauses(var);
         run_rule2=true;
         rule2num++;
      }
      else if (get_pos_clause_nb(var) == 0) {
         NB_MONO++;
         var_current_value[var] = FALSE;
         var_rest_value[var] = NONE;
         var_state[var] = PASSIVE;
         _push(var, VARIABLE_STACK);  //压进VARIABLE_STACK纪录
         remove_clauses(var);
         run_rule2=true;
         rule2num++;
      } 
      else if (nb_neg_clause_of_length1[var]+NB_EMPTY>=UB) {
         flag++;
         rule2num++;
         if (assign_value(var, FALSE, NONE)==NONE)  //被upperbound限制住了
            return NONE; 
         run_rule2=true;
      }
      else if (nb_pos_clause_of_length1[var]+NB_EMPTY>=UB) {
         rule2num++;
         flag++;
         if (assign_value(var, TRUE, NONE)==NONE) //被upperbound限制住了
             return NONE;
         run_rule2=true;
      }
      else if (nb_neg_clause_of_length1[var]>=
         nb_pos_clause_of_length1[var]+
         nb_pos_clause_of_length2[var]+ 
         nb_pos_clause_of_length3[var]) { //自带rule2
         flag++;
         rule2num++;
         if (assign_value(var, FALSE, NONE)==NONE) //被upperbound限制住了
             return NONE;
         run_rule2=true;
      }
      else if (nb_pos_clause_of_length1[var]>=
         nb_neg_clause_of_length1[var]+
         nb_neg_clause_of_length2[var]+ 
         nb_neg_clause_of_length3[var]) {  //自带rule2
         flag++;
         rule2num++;
         if (assign_value(var, TRUE, NONE)==NONE) //被upperbound限制住了
             return NONE;
         run_rule2=true;
      }
      else if (rule3(var)){
         rule3num++;
         run_rule2=true;
      }else if (rule4(var)){
         rule4num++;
      }
      else{
         if (nb_neg_clause_of_length1[var]>nb_pos_clause_of_length1[var]) { //记下较少的unit个数
              cont+=nb_pos_clause_of_length1[var];
         }
           else 
             cont+=nb_neg_clause_of_length1[var];  
      } 
    }
  } 
  }
  if (DEBUG_OPEN_RULE6){
    bool rule6flag=false;
    for (int var=0;var<NB_VAR;var++)
      if (var_state[var]==ACTIVE){ 
         if (rule6(var)) rule6flag=true;
      } 
    if (rule6flag) goto A;
  }
  if (cont+NB_EMPTY>=UB)
    return NONE;
  for (var = 0; var < NB_VAR; var++) {
    if (var_state[var] == ACTIVE) {
       reduce_if_positive[var]=nb_neg_clause_of_length1[var]*2+
                               nb_neg_clause_of_length2[var]*4+ 
                               nb_neg_clause_of_length3[var];
       reduce_if_negative[var]=nb_pos_clause_of_length1[var]*2+
                               nb_pos_clause_of_length2[var]*4+ 
                               nb_pos_clause_of_length3[var];
       poid=reduce_if_positive[var]*reduce_if_negative[var]*64+
                               reduce_if_positive[var]+reduce_if_negative[var];
       if (poid>max_poid) {
             chosen_var=var; 
             max_poid=poid;
       } 
    }
  }

  if (chosen_var == NONE) return FALSE;  //选出这个变量分支 

  saved_clause_stack[chosen_var] = CLAUSE_STACK_fill_pointer; //纪录在选择该变量时的各个栈位置
  saved_reducedclause_stack[chosen_var] = REDUCEDCLAUSE_STACK_fill_pointer;
  saved_unitclause_stack[chosen_var] = UNITCLAUSE_STACK_fill_pointer;
  saved_nb_empty[chosen_var]=NB_EMPTY;
  saved_nb_clause[chosen_var]=NB_CLAUSE;
  saved_saved_clauses[chosen_var]=SAVED_CLAUSES_fill_pointer;
  saved_new_clauses[chosen_var]=NEW_CLAUSES_fill_pointer;
  if (reduce_if_positive[chosen_var]<reduce_if_negative[chosen_var])
       return assign_value(chosen_var, TRUE, FALSE); //赋正
  else 
       return assign_value(chosen_var, FALSE, TRUE); //赋负

}

my_type var_best_value[tab_variable_size]; // Best assignment of variables  保存最优解
int get_current_value(int var){
  if (var_state[var]!=DONE) return var_current_value[var];   
  set<int>::iterator it;
  var_state[var]=PASSIVE;
  var_current_value[var]=0;
  for (it=recur[var].begin();it!=recur[var].end();it++){
      int lit=*it,value;
      if (lit<NB_VAR) value=get_current_value(lit);
                 else value=get_current_value(lit-NB_VAR); 
      if (lit<NB_VAR  && value==1) var_current_value[var]=1;
      if (lit>=NB_VAR && value==0) var_current_value[var]=1;
  }
  return var_current_value[var];
}
void update_current_value(){
  for (int var=0;var<NB_VAR;var++) 
    get_current_value(var); 
}
int dpl() { 
  int var, nb;
  do {
    if (VARIABLE_STACK_fill_pointer==NB_VAR) { //VARIABLE_STACK中元素个数等于样例的变量个数了
       UB=NB_EMPTY; 
       update_current_value();
       nb=verify_solution(var_current_value); //验证解
      // printf("nb=%d  NB_EMPTY=%d\n",nb,NB_EMPTY);
       if (nb!=NB_EMPTY) printf("problem nb...");
       printf("o %d\n", UB); //输出upper bound
       for (var = 0; var < NB_VAR; var++)
           var_best_value[var] = var_current_value[var]; //把解纪录下来?
       while (backtracking()==NONE); //把backtracking做到不能做
       if (VARIABLE_STACK_fill_pointer==0) break; //可以都处理完 break
      }
      if (UB-NB_EMPTY==1)
        if (unitclause_process() ==NONE) //upper bound没有限制死
            while (backtracking()==NONE);
      if (choose_and_instantiate_variable()==NONE)
        while (backtracking()==NONE); 
  }while (VARIABLE_STACK_fill_pointer > 0);
  return 0;
}

void init() { //初始化数据,都清空
  int var, clause;
  NB_EMPTY=0; REAL_NB_CLAUSE=NB_CLAUSE; //初始的NB_EMPTY为0   REAL_NB_CLAUSE纪录最初的CLAUSE个数
  UNITCLAUSE_STACK_fill_pointer=0;
  VARIABLE_STACK_fill_pointer=0;
  CLAUSE_STACK_fill_pointer = 0;
  REDUCEDCLAUSE_STACK_fill_pointer = 0;  //所有栈都清空
  for (var=0; var<NB_VAR; var++) {
    reason[var]=NO_REASON;
    fixing_clause[var]=NONE;
    fixing_clause[var+NB_VAR]=NONE;
    lit_involved_in_clause[var]=NONE;
    lit_involved_in_clause[var+NB_VAR]=NONE;
  }
  for (clause=0; clause<NB_CLAUSE; clause++) {
    lit_to_fix[clause]=NONE;
    clause_involved[clause]=NONE;
  }
}
 
int main(int argc, char *argv[]) {
  //freopen("output.txt","w",stdout);
  char saved_input_file[WORD_LENGTH];
  int i,  var; 
  long begintime, endtime, mess;
  struct tms *a_tms;
  FILE *fp_time;

  if (argc<2) {
    printf("Using format: maxsatz input_instance [upper_bound]\n");
    return FALSE;
  }
  for (i=0; i<WORD_LENGTH; i++) saved_input_file[i]=argv[1][i];

  a_tms = ( struct tms *) malloc( sizeof (struct tms));
  mess=times(a_tms); begintime = a_tms->tms_utime;

  switch (build_simple_sat_instance(argv[1])) {  //读入数据
  case FALSE: printf("Input file error\n"); return FALSE;
  case TRUE:
    if (argc>2) UB=atoi(argv[2]); else UB=NB_CLAUSE;  //Upperbound = NuberOfClause 或者 用户输入
    init();  //初始化    
    dpl();   //执行算法的代码
    break;
  case NONE: printf("An empty resolvant is found!\n"); break;
  }
  //-----输出-----
  mess=times(a_tms); endtime = a_tms->tms_utime;

  printf("\ns OPTIMUM FOUND\nc Optimal Solution (minimum number of unsatisfied clauses) = %d\n", UB);
  printf("v");
  for (i = 0; i < NB_VAR; i++) {
    if (var_best_value[i] == FALSE) //解纪录在var_best_value中
      printf(" -%i", i + 1); //注意i+1
    else
      printf(" %i", i + 1);
  }
  printf(" 0\n");
  printf("NB_MONO= %ld, NB_UNIT= %ld, NB_BRANCHE= %ld, NB_BACK= %ld \n", 
   NB_MONO, NB_UNIT, NB_BRANCHE, NB_BACK);
          
  printf ("Program terminated in %5.3f seconds.\n",
    ((double)(endtime-begintime)/CLK_TCK));

  fp_time = fopen("timetable", "a");
  fprintf(fp_time, "maxsatz14bis+fl %s %5.3f %ld %ld %d %d %d %d\n", 
    saved_input_file, ((double)(endtime-begintime)/CLK_TCK), 
    NB_BRANCHE, NB_BACK,  
    UB, NB_VAR, INIT_NB_CLAUSE, NB_CLAUSE-INIT_NB_CLAUSE);
  printf("maxsatz14bis+fl %s %5.3f %ld %ld %d %d %d %d\n", 
   saved_input_file, ((double)(endtime-begintime)/CLK_TCK), 
   NB_BRANCHE, NB_BACK,
   UB, NB_VAR, INIT_NB_CLAUSE, NB_CLAUSE-INIT_NB_CLAUSE);  
  printf("----RULE2: %d----\n",rule2num);
  printf("----RULE3: %d----\n",rule3num);
  printf("----RULE4: %d----\n",rule4num);
  printf("----RULE6: %d----\n",rule6num);
  printf("verify_solution: %d\n",verify_solution(var_best_value));
  fclose(fp_time);
  return TRUE;
}
