/*
Based on wpmsz-1.3.c, reformat some functions
*/

/* Based on wpmsz-1.4, with some optimizations
 */

/* Based on wpmsz-1.5, compute the minweight among clauses
involved in conflict, instead of among all clauses involved
in unit propagation
*/

/* Based on wpmsz-1.6, apply rule 1 and rule 2
Rule 1: 1 2, -1 2 ==> 1
Rule 2: 1, -1 ==> empty

*/

/* Based on wpmsz-2.0, merge binary clauses
 */

/* Based on wpmsz-2.2, apply cycle resolution
 */

/* Based on wpsmz-2.4, apply cycle resolution in an
inconsistent subset of clauses, when rules 5 and 6
are not applicable (i.e. other clauses implying
a cycle structure do not form a chain).
*/

/* Based on wpsmz, use arrays instead of linked lists for neg_in and pos_in
 */

/* before failed literal detection in lookahead(), do unit propagation
to fix all unit clauses. In this way, failed literal detection can obtain
smaller conflicting clause sets more easily
*/

/* Based on maxsatz2013, apply inference rules when beginning lookahead
to maximize inference rules.

When reducing clauses by assigning a value to a variable, if there are
several empty clauses, the first of those allowing rules 5 or 6 is returned
if any; otherwise, the first of those allowing rules 3 or 4 is returned
if any; otherwise, unit propagation continues
*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

#include <sys/types.h>
#include <limits.h>

#include <unistd.h>


#include <math.h>

typedef signed int my_type;
typedef unsigned int my_unsigned_type;

typedef long long int lli_type;

// #define DEBUG

#define WORD_LENGTH 512
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
#define tab_variable_size  60000
#define tab_clause_size 3000000
#define tab_unitclause_size ((tab_clause_size/4<2000) ? 2000 : tab_clause_size/4)
#define my_tab_variable_size ((tab_variable_size/2<1000) ? 1000 : tab_variable_size/2)
#define my_tab_clause_size ((tab_clause_size/2<2000) ? 2000 : tab_clause_size/2)
#define my_tab_unitclause_size ((tab_unitclause_size/2<1000) ? 1000 : tab_unitclause_size/2)
#define tab_literal_size 2*tab_variable_size
#define double_tab_clause_size 2*tab_clause_size
#define positive(literal) literal<NB_VAR
#define negative(literal) literal>=NB_VAR
#define get_var_from_lit(literal) \
  ((literal<NB_VAR) ? literal : literal-NB_VAR)
#define complement(lit1, lit2) \
 ((lit1<lit2) ? lit2-lit1 == NB_VAR : lit1-lit2 == NB_VAR)
#define get_lit(v, s) ((s == POSITIVE) ? v : v + NB_VAR)

#define tab_clause_size_XL (tab_clause_size * 10)

#define inverse_signe(signe) \
 (signe == POSITIVE) ? NEGATIVE : POSITIVE
#define unsat(val) (val==0)?"UNS":"SAT"
#define pop(stack) stack[--stack ## _fill_pointer]
#define _push(item, stack) stack[stack ## _fill_pointer++] = item
#define top(stack) stack[stack ## _fill_pointer - 1]
//#define satisfiable() CLAUSE_STACK_fill_pointer == NB_CLAUSE
#define min(a, b)  (((a) < (b)) ? (a) : (b))


#define NEGATIVE 0
#define POSITIVE 1
#define PASSIVE 0
#define ACTIVE 1
//------Debug------
#define DEBUG_OPEN_RULE3 true
#define DEBUG_OPEN_RULE6 false
#define DEBUG_OPEN_RULE6_1 false
#define DEBUG_RECUR true
#define MAX_LIT_NUM 4
#define DONE -2
//------Debug------
my_type var_current_value[tab_variable_size]; // Current assignment of variables
my_type var_rest_value[tab_variable_size]; // Restore vaule of variables
my_type var_state[tab_variable_size]; // Variable status

int saved_lit_in_stack[tab_variable_size];
int saved_clause_stack[tab_variable_size];
int saved_reducedclause_stack[tab_variable_size];
int saved_unitclause_stack[tab_variable_size];
lli_type saved_nb_empty[tab_variable_size];
lli_type nb_neg_clause_of_length1[tab_variable_size];
lli_type nb_pos_clause_of_length1[tab_variable_size];
lli_type nb_neg_clause_of_length2[tab_variable_size];
lli_type nb_neg_clause_of_length3[tab_variable_size];
lli_type nb_pos_clause_of_length2[tab_variable_size];
lli_type nb_pos_clause_of_length3[tab_variable_size];

float reduce_if_negative[tab_variable_size];
float reduce_if_positive[tab_variable_size];
int *sat[tab_clause_size]; // Clauses [clause][literal]
int *var_sign[tab_clause_size]; // Clauses [clause][var,sign]
lli_type clause_weight[tab_clause_size]; // Clause weights
lli_type ini_clause_weight[tab_clause_size]; // Initial clause weights
my_type clause_state[tab_clause_size]; // Clause status
int clause_length[tab_clause_size]; // Clause length

int VARIABLE_STACK_fill_pointer = 0;
int CLAUSE_STACK_fill_pointer = 0;
int UNITCLAUSE_STACK_fill_pointer = 0;
int REDUCEDCLAUSE_STACK_fill_pointer = 0;


int VARIABLE_STACK[tab_variable_size];
int CLAUSE_STACK[tab_clause_size];
int UNITCLAUSE_STACK[tab_unitclause_size];
int REDUCEDCLAUSE_STACK[tab_clause_size];

int PREVIOUS_REDUCEDCLAUSE_STACK_fill_pointer = 0;

lli_type HARD_WEIGHT = 0;
int NB_VAR;
int NB_CLAUSE;
int INIT_NB_CLAUSE;
int INIT_NB_CLAUSE_PREPROC;
int REAL_NB_CLAUSE;
#define INIT_BASE_NB_CLAUSE (tab_clause_size / 2)
int BASE_NB_CLAUSE = INIT_BASE_NB_CLAUSE;

lli_type NB_MONO=0, NB_BRANCHE=0, NB_BACK = 0;
lli_type NB_EMPTY=0, UB;
int instance_type;
int partial;

#define NO_CONFLICT -3
#define NO_REASON -3
int reason[tab_variable_size];
int REASON_STACK[tab_variable_size];
int REASON_STACK_fill_pointer=0;

int MY_UNITCLAUSE_STACK[tab_unitclause_size];
int MY_UNITCLAUSE_STACK_fill_pointer=0;
int CANDIDATE_LITERALS[2*tab_variable_size];
int CANDIDATE_LITERALS_fill_pointer=0;
int NEW_CLAUSES[tab_clause_size][7];
int NEW_CLAUSES_fill_pointer=0;
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

int CLAUSES_TO_REMOVE[tab_clause_size];
int CLAUSES_TO_REMOVE_fill_pointer=0;
lli_type WEIGHTS_TO_REMOVE[tab_clause_size];
int WEIGHTS_TO_REMOVE_fill_pointer=0;
lli_type CLAUSES_WEIGHTS_TO_REMOVE[tab_clause_size];
int CLAUSES_WEIGHTS_TO_REMOVE_fill_pointer=0;

my_type var_best_value[tab_variable_size]; // Best assignment of variables
int SAVED_WEIGHTS_CLAUSE[tab_clause_size];
int SAVED_WEIGHTS_CLAUSE_fill_pointer = 0;
lli_type SAVED_WEIGHTS_WEIGHT[tab_clause_size];
int SAVED_WEIGHTS_WEIGHT_fill_pointer = 0;
int saved_weights_nb[tab_variable_size];

int MARK_STACK[tab_variable_size * 2];
int MARK_STACK_fill_pointer = 0;
int mark[tab_variable_size * 2];

int IG_STACK[tab_unitclause_size];
int IG_STACK_fill_pointer;
int POST_UIP_LITS[tab_variable_size];
int POST_UIP_LITS_fill_pointer;
int NEW_CLAUSE_LITS[tab_variable_size];
int NEW_CLAUSE_LITS_fill_pointer;
int unit_of_var[tab_variable_size];
#define max_var_learned (tab_variable_size / 10)
int undo_learned[tab_variable_size][max_var_learned];
int nb_undo_learned[tab_variable_size];
#define MAX_LEN_LEARNED 20 // MAX_LEN_LEARNED = num_lits * 2 (best performance 20)

/* --------------------------*/
int *neg_in[tab_variable_size];
int *pos_in[tab_variable_size];
int neg_nb[tab_variable_size];
int pos_nb[tab_variable_size];
int saved_pos_nb[tab_variable_size];
int saved_neg_nb[tab_variable_size];
int POS_NEG_FOR_BACKTRACKING_STACK[tab_clause_size_XL];
int POS_NEG_FOR_BACKTRACKING_STACK_fill_pointer= 0;
int saved_saved_pos_neg[tab_variable_size];
//int clause_involved_fl[tab_clause_size];

lli_type simple_get_pos_clause_nb(int);
lli_type simple_get_neg_clause_nb(int);
//int avoid[tab_variable_size];

int in_conflict[tab_clause_size];
int CONFLICTCLAUSE_STACK[tab_clause_size];
int CONFLICTCLAUSE_STACK_fill_pointer=0;
int JOINT_CONFLICT;
int CREATED_UNITCLAUSE_STACK[tab_clause_size];
int CREATED_UNITCLAUSE_STACK_fill_pointer=0;
lli_type saved_indexsize_neg[tab_variable_size];
lli_type saved_indexsize_pos[tab_variable_size];
int instance_length=FALSE;
#define new_clause_nb 2000
int treat_complementary_unitclauses(int var, int clause);


void add_newclause_in(int var, int sign){
  if(sign== POSITIVE) {
     if(pos_nb[var]+1>=saved_indexsize_pos[var]){
       pos_in[var]=(int *)realloc(pos_in[var],(saved_indexsize_pos[var]+new_clause_nb) * sizeof(int));
	saved_indexsize_pos[var]+=new_clause_nb;
       if(!pos_in[var]) {printf("assignment failed\n"); }
	}
		pos_in[var][pos_nb[var]++]=NB_CLAUSE;
		pos_in[var][pos_nb[var]]=NONE;

  }
  else{
      if(neg_nb[var]+1>=saved_indexsize_neg[var]){
       neg_in[var]=(int *)realloc(neg_in[var],(saved_indexsize_neg[var]+new_clause_nb) * sizeof(int));
	saved_indexsize_neg[var]+=new_clause_nb;
	if(!neg_in[var]) {printf("assignment failed\n"); }
	}
	    neg_in[var][neg_nb[var]++]=NB_CLAUSE;
	    neg_in[var][neg_nb[var]]=NONE;
  }
  _push(var, POS_NEG_FOR_BACKTRACKING_STACK);
  _push(sign, POS_NEG_FOR_BACKTRACKING_STACK);
}


void zz_print_structure(){
	int i, var, clause, *clauses,k=0;

	//~ printf("NB_VAR= %d, NB_CLAUSE-BASE_NB_CLAUSE= %d \n", NB_VAR, NB_CLAUSE-BASE_NB_CLAUSE);
	//~ printf("-----var list : \n------");
	for(i=0; i<NB_VAR; i++){
		k=0;
		//~ printf("var= %d : \n", i);
		//~ printf("pos_in: ");
		clauses =pos_in[i];
		for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
			//~ printf("%d, ", clause);
			k++;
		}
		if(k!= pos_nb[i])
					printf(" bizarre inprint structure \n");
		//~ printf("\nneg_in: ");
		//~ clauses =neg_in[i];
		//~ for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
			//~ printf("%d, ", clause);
		//~ }
		//~ printf("\n");
	//~ }
	//~ printf("-----clause list first10 : \n------");
	//~ for(i= BASE_NB_CLAUSE; i<= NB_CLAUSE; i++){
		//~ printf("%d, ", i);
	}
	//~ printf("\n");
}

// #include "input.c" //

/* test if the new clause is redundant or subsompted by another */
#define OLD_CLAUSE_REDUNDANT -77
#define NEW_CLAUSE_REDUNDANT -7

int smaller_than(int lit1, int lit2) {
  return ((lit1<NB_VAR) ? lit1 : lit1-NB_VAR) <
    ((lit2<NB_VAR) ? lit2 : lit2-NB_VAR);
}

int redundant(int *new_clause, int *old_clause) {
  int lit1, lit2, old_clause_diff=0, new_clause_diff=0;

  lit1=*old_clause; lit2=*new_clause;
  while ((lit1 != NONE) && (lit2 != NONE)) {
    if (smaller_than(lit1, lit2)) {
      lit1=*(++old_clause); old_clause_diff++;
    } else if (smaller_than(lit2, lit1)) {
      lit2=*(++new_clause); new_clause_diff++;
    } else if (complement(lit1, lit2)) {
      return FALSE; /* old_clause_diff++; new_clause_diff++; j1++; j2++; */
    } else {
      lit1=*(++old_clause);  lit2=*(++new_clause);
    }
  }
  if ((lit1 == NONE) && (old_clause_diff == 0))
    /* la nouvelle clause est redondante ou subsumee */
    return NEW_CLAUSE_REDUNDANT;
  if ((lit2 == NONE) && (new_clause_diff == 0))
    /* la old clause est redondante ou subsumee */
    return OLD_CLAUSE_REDUNDANT;
  return FALSE;
}

void remove_passive_clauses() {
  int  clause, put_in, first=NONE;
  for (clause = BASE_NB_CLAUSE; clause < NB_CLAUSE; clause++) {
    if (clause_state[clause]==PASSIVE) {
      first=clause; break;
    }
  }
  if (first!=NONE) {
    put_in=first;
    for(clause=first+1; clause<NB_CLAUSE; clause++) {
      if (clause_state[clause]==ACTIVE) {
	sat[put_in]=sat[clause]; var_sign[put_in]=var_sign[clause];
	clause_state[put_in]=ACTIVE;
	clause_length[put_in]=clause_length[clause];
	clause_weight[put_in]=clause_weight[clause];
	put_in++;
      }
    }
    NB_CLAUSE=put_in;
  }
}

void remove_passive_vars_in_clause(int clause) {
  int *vars_signs, *vars_signs1, var, var1, first=NONE;

  vars_signs=var_sign[clause];
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
    if (var_state[var]!=ACTIVE) {
      first=var; break;
    }
  }
  if (first!=NONE) {
    for(vars_signs1=vars_signs+2, var1=*vars_signs1;
	var1!=NONE; var1=*(vars_signs1+=2)) {
      if (var_state[var1]==ACTIVE) {
	*vars_signs=var1; *(vars_signs+1) = *(vars_signs1+1);
	vars_signs+=2;
      }
    }
    *vars_signs=NONE;
  }
}


int clean_structure() {
  int clause, var, *vars_signs;

  remove_passive_clauses();
  if (NB_CLAUSE == BASE_NB_CLAUSE)
    return FALSE;
  for (clause = BASE_NB_CLAUSE; clause < NB_CLAUSE; clause++)
    remove_passive_vars_in_clause(clause);

  for (var = 0; var < NB_VAR; var++) {
	neg_nb[var] = 0;
    pos_nb[var] = 0;
  }
  for (clause=BASE_NB_CLAUSE; clause<NB_CLAUSE; clause++) {
    vars_signs=var_sign[clause];
    for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
      if (*(vars_signs+1)==POSITIVE)
	pos_in[var][pos_nb[var]++]=clause;
      else  neg_in[var][neg_nb[var]++]=clause;
    }
  }
  for (var=0; var<NB_VAR; var++) {
    neg_in[var][neg_nb[var]]=NONE;
    pos_in[var][pos_nb[var]]=NONE;
  }
  return TRUE;
}


void lire_clauses(FILE *fp_in, int instance_type) {
  int i, j, jj, ii, length, tautologie, lits[10000], lit, lit1;
  lli_type weight;

  partial = 0;
  if (HARD_WEIGHT > 0) // For partial
    partial = 1;
  for (i = BASE_NB_CLAUSE; i < NB_CLAUSE; i++) {
    length=0;
    if (instance_type != 0)
      fscanf(fp_in, "%lli", &weight);
    else
      weight = 1;
    fscanf(fp_in, "%d", &lits[length]);
    while (lits[length] != 0) {
      length++;
      fscanf(fp_in, "%d", &lits[length]);
    }
    tautologie = FALSE;
    /* test if some literals are redundant and sort the clause */
    for (ii=0; ii<length-1; ii++) {
      lit = lits[ii];
      for (jj=ii+1; jj<length; jj++) {
	if (abs(lit)>abs(lits[jj])) { // swap
	  lit1=lits[jj]; lits[jj]=lit; lit=lit1;
	} else if (lit == lits[jj]) { // x v x = x
	  lits[jj] = lits[length-1];
	  jj--; length--; lits[length] = 0;
	  printf("literal %d is redundant in clause %d \n",
		 lit, i+1);
	} else if (abs(lit) == abs(lits[jj])) { // x v -x = T
	  tautologie = TRUE; break;
	}
      }
      if (tautologie == TRUE) break;
      else lits[ii] = lit;
    }
    if (tautologie == FALSE) {
      sat[i]= (int *)malloc((length+1) * sizeof(int));
      for (j=0; j<length; j++) {
	if (lits[j] < 0)
	  sat[i][j] = abs(lits[j]) - 1 + NB_VAR ;
	else
	  sat[i][j] = lits[j]-1;
      }
      sat[i][length]=NONE;
      clause_length[i]=length;
      clause_weight[i] = weight;
      if (partial == 0)
	HARD_WEIGHT += weight;
      clause_state[i] = ACTIVE;
    } else {
      i--;
      NB_CLAUSE--;
    }
  }
}

void build_structure() {
  int i, j, var, *lits1, length, clause, *vars_signs, lit;
  int *clique_set;
  for (i=0; i<NB_VAR; i++) {
    neg_nb[i] = 0; pos_nb[i] = 0;
  }
  for (i=BASE_NB_CLAUSE; i<NB_CLAUSE; i++) {
    for(j=0; j<clause_length[i]; j++) {
      if (sat[i][j]>=NB_VAR) {
	var=sat[i][j]-NB_VAR; neg_nb[var]++;
      }
      else {
	var=sat[i][j]; pos_nb[var]++;
      }
    }
    if (sat[i][clause_length[i]] !=NONE)
      printf("erreur ");
  }
  for(clause=BASE_NB_CLAUSE;clause<NB_CLAUSE;clause++) {
    length = clause_length[clause];
     if(length>2)
	instance_length=TRUE;
    var_sign[clause] = (int *)malloc((2*length+1)*sizeof(int));
    //~ flag_in_stack[clause]= FALSE;
    lits1 = sat[clause]; vars_signs = var_sign[clause];
    for(lit=*lits1; lit!=NONE; lit=*(++lits1),(vars_signs+=2)) {
      if (negative(lit)) {
	*(vars_signs+1)= NEGATIVE;
	*vars_signs = get_var_from_lit(lit);
      }
      else {
	*(vars_signs+1)=POSITIVE;
	*vars_signs = lit;
      }
    }
    *vars_signs = NONE;
  }
  for (i=0; i<NB_VAR; i++) {
    saved_indexsize_neg[i]=128*neg_nb[i];
    neg_in[i] = (int *)malloc(saved_indexsize_neg[i] * sizeof(int));
    saved_indexsize_pos[i]=128*pos_nb[i];
    pos_in[i] = (int *)malloc(saved_indexsize_pos[i] * sizeof(int));
    neg_in[i][neg_nb[i]]=NONE; pos_in[i][pos_nb[i]]=NONE;
    neg_nb[i] = 0; pos_nb[i] = 0;
    var_state[i] = ACTIVE;
  }
  for (i=BASE_NB_CLAUSE; i<NB_CLAUSE; i++) {
    lits1 = sat[i];
    for(lit=*lits1; lit!=NONE; lit=*(++lits1)) {
      if (positive(lit))
	pos_in[lit][pos_nb[lit]++] = i;
      else
	neg_in[get_var_from_lit(lit)]
	  [neg_nb[get_var_from_lit(lit)]++] = i;
    }
  }
}

void eliminate_redundance() {
  int i;

  for (i = BASE_NB_CLAUSE; i < NB_CLAUSE; i++) {
    if (clause_state[i]==ACTIVE) {
      if (clause_length[i]==1)
	_push(i, UNITCLAUSE_STACK);
    }
  }
}

int build_simple_sat_instance(char *input_file) {
  FILE* fp_in=fopen(input_file, "r");
  char ch, word2[WORD_LENGTH];
  int i;
  char pLine[WORD_LENGTH];
  if (fp_in == NULL) {
    return FALSE;
  }

  fscanf(fp_in, "%c", &ch);
  while (ch!='p') {
    while (ch!='\n') fscanf(fp_in, "%c", &ch);
    fscanf(fp_in, "%c", &ch);
  }
  i = 0;
  while (ch != '\n') {
    pLine[i] = ch;
    i++;
    fscanf(fp_in, "%c", &ch);
  }
  sscanf(pLine, "p %s %d %d %lli",
	 word2, &NB_VAR, &NB_CLAUSE, &HARD_WEIGHT);
  if (NB_VAR > tab_variable_size ||
      NB_CLAUSE > tab_clause_size - INIT_BASE_NB_CLAUSE) {
    printf("ERROR: Out of memory.\n");
    exit(0);
  }
  NB_CLAUSE = NB_CLAUSE + BASE_NB_CLAUSE;
  INIT_NB_CLAUSE = NB_CLAUSE;
  if (strcmp(word2, "cnf") == 0)
    instance_type = 0; // cnf
  else {
    instance_type = 1; // wcnf
  }
  lire_clauses(fp_in, instance_type);
  fclose(fp_in);
  build_structure();
  eliminate_redundance();
  if (clean_structure()==FALSE)
    return FALSE;
  return TRUE;
}

// end of input.c

void print_clause(int clause) {
  int *vars_signs, var;

  printf("(%i, %i, %i) [%lli] ", clause, clause_length[clause],
	 clause_state[clause], clause_weight[clause]);
  vars_signs = var_sign[clause];
  for(var = *vars_signs; var != NONE; var = *(vars_signs += 2)) {
    if (*(vars_signs + 1) == NEGATIVE)
      printf("-");
    printf("%i ", var + 1);
  }
  printf("0");
}

void remove_clauses(int var) {
  register int clause, *clauses;
  int p_clause;

  if (var_current_value[var] == POSITIVE)
    clauses =pos_in[var];
  else
      clauses =neg_in[var];
  for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
     if (clause_state[clause] == ACTIVE) {
      clause_state[clause] = PASSIVE;
      _push(clause, CLAUSE_STACK);
    }
  }
}

int reduce_clauses(int var) {
  register int clause, *clauses;
  int p_clause;

  if (var_current_value[var] == POSITIVE)
    clauses =neg_in[var];
  else
       clauses =pos_in[var];
   for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if (clause_state[clause] == ACTIVE) {
      clause_length[clause]--;
      _push(clause, REDUCEDCLAUSE_STACK);
      switch (clause_length[clause]) {
      case 0:
	NB_EMPTY += clause_weight[clause];
	if (UB<=NB_EMPTY) { /// Test if this check is needed
	  _push(clause, IG_STACK);
	  _push(var, MARK_STACK);
	  mark[var] = MARK_STACK_fill_pointer;
	  unit_of_var[var] = clause;
	  return NONE;
	}
	break;
      case 1:
	_push(clause, UNITCLAUSE_STACK);
#ifdef DEBUG
	if (UNITCLAUSE_STACK_fill_pointer > tab_unitclause_size - 5) {
	  printf("DEBUG: UNITCLAUSE_STACK.\n");
	  exit(0);
	}
#endif
	break;
      }
    }
  }
  return TRUE;
}

int my_reduce_clauses(int var) {
  register int clause, *clauses;
  int p_clause;

  if (var_current_value[var] == POSITIVE)
    clauses =neg_in[var];

  else
     clauses =pos_in[var];
   for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if (clause_state[clause] == ACTIVE) {
      clause_length[clause]--;
      _push(clause, REDUCEDCLAUSE_STACK);
      switch (clause_length[clause]) {
      case 0:
	return clause;
      case 1:
	_push(clause, MY_UNITCLAUSE_STACK);
#ifdef DEBUG
	if (MY_UNITCLAUSE_STACK_fill_pointer > tab_unitclause_size - 5) {
	  printf("DEBUG: MY_UNITCLAUSE_STACK.\n");
	  exit(0);
	}
#endif
	break;
      }
    }
  }
  return NO_CONFLICT;
}

int my_reduce_clauses_for_fl(int var) {
  register int clause, *clauses;
  int p_clause;

  if (var_current_value[var] == POSITIVE)
    clauses =neg_in[var];
  else
      clauses =pos_in[var];
   for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if (clause_state[clause] == ACTIVE) {
      clause_length[clause]--;
      _push(clause, REDUCEDCLAUSE_STACK);
      switch (clause_length[clause]) {
      case 0:
	return clause;
      case 1:
	_push(clause, UNITCLAUSE_STACK);
	break;
      }
    }
  }
  return NO_CONFLICT;
}

void print_values(int nb_var) {
  FILE* fp_out;
  int i;
  fp_out = fopen("satx.sol", "w");
  for (i=0; i<nb_var; i++) {
    if (var_current_value[i] == 1)
      fprintf(fp_out, "%d ", i+1);
    else
      fprintf(fp_out, "%d ", 0-i-1);
  }
  fprintf(fp_out, "\n");
  fclose(fp_out);
}
//-----------------------------
int needRecur[tab_variable_size];
//-----------------------------
int backtracking() {
  int var, index,clause, saved;
  int *vars_signs, var_s, sign, v;

  NB_BACK++;
  //~ printf("NB_BACK= %lld var= %d, before backtracking: \n", NB_BACK, var);
  //~ zz_print_structure();

  while (VARIABLE_STACK_fill_pointer > 0) {
    var = pop(VARIABLE_STACK);

    if (nb_undo_learned[var] > 0) {
      for (index = 0; index < nb_undo_learned[var]; index++) {
	clause = undo_learned[var][index];
	clause_length[clause]++;
      }
      nb_undo_learned[var] = 0;
    }
    if (var_rest_value[var] == NONE){
      needRecur[var]=0;
      var_state[var] = ACTIVE;
    }
    else {
      for (index = saved_clause_stack[var];
	   index < CLAUSE_STACK_fill_pointer; index++)
	clause_state[CLAUSE_STACK[index]] = ACTIVE;
      CLAUSE_STACK_fill_pointer = saved_clause_stack[var];
      for (index = saved_reducedclause_stack[var];
	   index < REDUCEDCLAUSE_STACK_fill_pointer; index++) {

	clause_length[REDUCEDCLAUSE_STACK[index]]++;
      }
      REDUCEDCLAUSE_STACK_fill_pointer = saved_reducedclause_stack[var];
      UNITCLAUSE_STACK_fill_pointer=saved_unitclause_stack[var];
      NB_EMPTY=saved_nb_empty[var];
      NB_CLAUSE=saved_nb_clause[var];
      NEW_CLAUSES_fill_pointer=saved_new_clauses[var];
      saved= saved_saved_pos_neg[var];

      for(index= POS_NEG_FOR_BACKTRACKING_STACK_fill_pointer -1; index>= saved; index-=2){
		  sign= POS_NEG_FOR_BACKTRACKING_STACK[index];
		  v= POS_NEG_FOR_BACKTRACKING_STACK[index-1];
		  if(sign==POSITIVE){
			pos_nb[v]--; pos_in[v][pos_nb[v]]= NONE;
			if(pos_nb[v]<=0)
				printf("bizarre pos\n");
		  }
		  if(sign==NEGATIVE){
			neg_nb[v]--; neg_in[v][neg_nb[v]]= NONE;
			if(neg_nb[v]<=0)
				printf("bizarre neg\n");
		  }
	  }
      POS_NEG_FOR_BACKTRACKING_STACK_fill_pointer= saved;

      saved = saved_weights_nb[var];
      for (index = SAVED_WEIGHTS_CLAUSE_fill_pointer - 1;
	   index >= saved; index--)
	clause_weight[SAVED_WEIGHTS_CLAUSE[index]] =
	  SAVED_WEIGHTS_WEIGHT[index];
      SAVED_WEIGHTS_CLAUSE_fill_pointer = saved;
      SAVED_WEIGHTS_WEIGHT_fill_pointer = saved;

      if (NB_EMPTY<UB) {
	var_current_value[var] = var_rest_value[var];
	var_rest_value[var] = NONE;
	_push(var, VARIABLE_STACK);
	if (reduce_clauses(var)==NONE)
	  return NONE;
	remove_clauses(var);
	return TRUE;
      } else{
          needRecur[var]=0;
	        var_state[var] = ACTIVE;
      }
    }
  }

  return FALSE;
}

int verify_solution() {
  int i, var, *vars_signs, clause_truth;
  lli_type nb = 0;

  for (i = INIT_BASE_NB_CLAUSE; i < REAL_NB_CLAUSE; i++) {
    clause_truth = FALSE;
    vars_signs = var_sign[i];
    for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2))
      if (*(vars_signs+1) == var_current_value[var] ) {
	clause_truth = TRUE;
	break;
      }
    if (clause_truth == FALSE) {
      nb += ini_clause_weight[i];
    }
  }
  return nb;
}

void reset_context(int saved_clause_stack_fill_pointer,
		   int saved_reducedclause_stack_fill_pointer,
		   int saved_unitclause_stack_fill_pointer,
		   int saved_variable_stack_fill_pointer) {
  int index, var, clause;
  for (index = saved_clause_stack_fill_pointer;
       index < CLAUSE_STACK_fill_pointer; index++)
    clause_state[CLAUSE_STACK[index]] = ACTIVE;
  CLAUSE_STACK_fill_pointer = saved_clause_stack_fill_pointer;

  for (index = saved_reducedclause_stack_fill_pointer;
       index < REDUCEDCLAUSE_STACK_fill_pointer; index++) {
    clause = REDUCEDCLAUSE_STACK[index];
    clause_length[REDUCEDCLAUSE_STACK[index]]++;
  }
  REDUCEDCLAUSE_STACK_fill_pointer =
    saved_reducedclause_stack_fill_pointer;

  for(index=saved_variable_stack_fill_pointer;
      index<VARIABLE_STACK_fill_pointer; index++) {
    var=VARIABLE_STACK[index];
    reason[var]=NO_REASON;
    needRecur[var]=0;
    var_state[var]=ACTIVE;
  }
  VARIABLE_STACK_fill_pointer=saved_variable_stack_fill_pointer;
  UNITCLAUSE_STACK_fill_pointer=saved_unitclause_stack_fill_pointer;
}

void create_binaryclause(int var1, int sign1, int var2, int sign2, lli_type min_weight) {
  int *vars_signs;

  vars_signs=NEW_CLAUSES[NEW_CLAUSES_fill_pointer++];
  if (var1<var2) {
    vars_signs[0]=var1; vars_signs[1]=sign1;
    vars_signs[2]=var2; vars_signs[3]=sign2;
  } else {
    vars_signs[0]=var2; vars_signs[1]=sign2;
    vars_signs[2]=var1; vars_signs[3]=sign1;
  }
  vars_signs[4]=NONE;
  var_sign[NB_CLAUSE]=vars_signs;
  clause_state[NB_CLAUSE]=ACTIVE;
  clause_length[NB_CLAUSE]=2;
  clause_weight[NB_CLAUSE] = min_weight;

  add_newclause_in(var1, sign1);
  add_newclause_in(var2, sign2);

  NB_CLAUSE++;
#ifdef DEBUG
  if (NB_CLAUSE > tab_clause_size - 5) {
    printf("DEBUG: NB_CLAUSE.\n");
    exit(0);
  }
#endif
}

int verify_binary_clauses(int *varssigns, int var1, int sign1,
			  int var2, int sign2) {
  //int nb=0;

  if (var1==*varssigns) {
    if ((*(varssigns+1)!=1-sign1) || (var2!=*(varssigns+2)) ||
	(*(varssigns+3)!=1-sign2)) {
      printf("VBC problem..");
      return FALSE;
    }
  }
  else {
    if ((var2 != *varssigns) ||
	(*(varssigns+1)!=1-sign2) ||
	(var1!=*(varssigns+2)) ||
	(*(varssigns+3)!=1-sign1)) {
      printf("VBC problem..");
      return FALSE;
    }
  }
  return TRUE;
}

int LINEAR_REASON_STACK1[tab_clause_size];
int LINEAR_REASON_STACK1_fill_pointer=0;
int LINEAR_REASON_STACK2[tab_clause_size];
int LINEAR_REASON_STACK2_fill_pointer=0;
int clause_involved[tab_clause_size];
int clause_entered[tab_clause_size];

int search_linear_reason1(int var) {
  int *vars_signs, clause, fixed_var, index_var, new_fixed_var;

  for(fixed_var=var; fixed_var!=NONE; fixed_var=new_fixed_var) {
    clause=reason[fixed_var];
    vars_signs = var_sign[clause];
    new_fixed_var=NONE;
    _push(clause, LINEAR_REASON_STACK1);
    clause_involved[clause]=TRUE;
    for(index_var=*vars_signs; index_var!=NONE;
	index_var=*(vars_signs+=2)) {
      if ((index_var!=fixed_var) && (reason[index_var]!=NO_REASON)) {
	if (new_fixed_var==NONE)
	  new_fixed_var=index_var;
	else {
	  return FALSE;
	}
      }
    }
  }
  return TRUE;
}

#define SIMPLE_NON_LINEAR_CASE 2
#define SIMPLE_RS1_NON_LINEAR_CASE 3
#define SIMPLE_RS2_NON_LINEAR_CASE 4
#define SIMPLE_CUB_NON_LINEAR_CASE 5
#define SIMPLE_RS1_3_NON_LINEAR_CASE 6
#define SIMPLE_RS2_3_NON_LINEAR_CASE 7

int search_linear_reason2(int var) {
  int *vars_signs, clause, fixed_var, index_var, new_fixed_var;

  for(fixed_var=var; fixed_var!=NONE; fixed_var=new_fixed_var) {
    clause=reason[fixed_var];
    if (clause_involved[clause]==TRUE) {
      if (LINEAR_REASON_STACK2_fill_pointer == 2 &&
	  LINEAR_REASON_STACK1_fill_pointer > 2 &&
	  LINEAR_REASON_STACK1[ 2 ] == clause)
	return SIMPLE_NON_LINEAR_CASE;
      else if (LINEAR_REASON_STACK2_fill_pointer == 2 &&
	       LINEAR_REASON_STACK1_fill_pointer > 3 &&
	       LINEAR_REASON_STACK1[ 3 ] == clause)
	return SIMPLE_RS2_NON_LINEAR_CASE;
      else if (LINEAR_REASON_STACK2_fill_pointer == 3 &&
	       LINEAR_REASON_STACK1_fill_pointer > 2 &&
	       LINEAR_REASON_STACK1[ 2 ] == clause)
	return SIMPLE_RS1_NON_LINEAR_CASE;

      else
	return FALSE;
    } else
      _push(clause, LINEAR_REASON_STACK2);
    vars_signs = var_sign[clause];
    new_fixed_var=NONE;
    for(index_var=*vars_signs; index_var!=NONE;
	index_var=*(vars_signs+=2)) {
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
	//int var, *vars_signs, var1, var2, flag;
  int var, *vars_signs, flag;

  if ((reason[varssigns[0]]!=clause1) || (reason[varssigns[2]]!=clause))
    return FALSE;
  vars_signs = var_sign[clause2];
  flag=FALSE;
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
    if ((varssigns[2]==var) && (reason[var]!=NO_REASON) &&
	(*(vars_signs+1) != var_current_value[var])) {
      flag=TRUE;
    }
  }
  return flag;
}

int create_complementary_binclause(int clause, int clause1, int clause2, lli_type min_weight) {
  int var, *vars_signs, i=0, varssigns[4], sign;
  vars_signs = var_sign[clause];
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
    if (reason[var]!=NO_REASON) {
      varssigns[i++]=var; varssigns[i++]=*(vars_signs+1);
    }
  }
  if (reason[varssigns[2]]==clause1) {
    var=varssigns[2];
    sign=varssigns[3];
    varssigns[2]=varssigns[0];
    varssigns[3]=varssigns[1];
    varssigns[0]=var;
    varssigns[1]=sign;
  }
#ifdef DEBUG
  if ((i!=4) || (check_reason(varssigns, clause, clause1, clause2)==FALSE))
    printf("CCB problem...");
#endif
  create_binaryclause(varssigns[0], 1-varssigns[1],
		      varssigns[2], 1-varssigns[3], min_weight);
  return TRUE;
}

int get_satisfied_literal(int clause) {
  int var, *vars_signs;

  vars_signs = var_sign[clause];
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
    if (*(vars_signs+1) == var_current_value[var])
      return var;
  }
  printf("ERROR: Satisfied literal not found.\n");
  return NONE;
}

int create_new_unitclause(int var, int sign, lli_type min_weight) {
 int *vars_signs;

  vars_signs=NEW_CLAUSES[NEW_CLAUSES_fill_pointer++];
  vars_signs[0]=var;
  vars_signs[1]=sign;
  vars_signs[2]=NONE;
  var_sign[NB_CLAUSE] = vars_signs;
  clause_state[NB_CLAUSE] = ACTIVE;
  clause_length[NB_CLAUSE] = 1;
  clause_weight[NB_CLAUSE] = min_weight;

  add_newclause_in(var,sign);

  NB_CLAUSE++;
  return NB_CLAUSE-1;
}

void create_ternary_clauses(int var1, int sign1, int var2, int sign2,
			                      int var3, int sign3, lli_type min_weight) {
  int *vars_signs;

  vars_signs=NEW_CLAUSES[NEW_CLAUSES_fill_pointer++];
  vars_signs[0]=var1; vars_signs[1]=sign1;
  vars_signs[2]=var2; vars_signs[3]=sign2;
  vars_signs[4]=var3; vars_signs[5]=sign3;
  vars_signs[6]=NONE;
  var_sign[NB_CLAUSE] = vars_signs;
  clause_state[NB_CLAUSE] = ACTIVE;
  clause_length[NB_CLAUSE] = 3;
  clause_weight[NB_CLAUSE] = min_weight;

  add_newclause_in(var1,sign1);
  add_newclause_in(var2,sign2);
  add_newclause_in(var3,sign3);

  NB_CLAUSE++;
#ifdef DEBUG
  if (NB_CLAUSE > tab_clause_size - 5) {
    printf("DEBUG: NB_CLAUSE.\n");
    exit(0);
  }
#endif
}

int non_linear_conflict(int empty_clause,
			int var1, int sign1,
			int var2, int sign2,
			lli_type min_weight) {
  int var, sign, j;
  // driving unit clause is LINEAR_REASON_STACK1[2] (propagate
  // it resulting the empty_clause by simple non-linear derivation
  // var1, sign1, var2, and sign2 are the two literals of empty_clause

  var = get_satisfied_literal(LINEAR_REASON_STACK1[2]);
  sign = var_current_value[var];
  for(j = 2; j < LINEAR_REASON_STACK1_fill_pointer - 1; j++) {
    create_complementary_binclause(LINEAR_REASON_STACK1[j],
				   LINEAR_REASON_STACK1[j+1],
				   LINEAR_REASON_STACK1[j-1],
				   min_weight);
  }
  create_ternary_clauses(var, sign, var1, sign1, var2, sign2, min_weight);
  create_ternary_clauses(var, 1-sign, var1, 1-sign1, var2, 1-sign2, min_weight);
  return TRUE;
}

int non_linear_conflict_rs1(int empty_clause,
			    int var1, int sign1,
			    int var2, int sign2,
			    lli_type min_weight) {
  int var, sign, j;
  int svar, ssign;

  var = get_satisfied_literal(LINEAR_REASON_STACK1[2]);
  sign = var_current_value[var];
  for(j = 2; j < LINEAR_REASON_STACK1_fill_pointer - 1; j++) {
    create_complementary_binclause(LINEAR_REASON_STACK1[j],
				   LINEAR_REASON_STACK1[j+1],
				   LINEAR_REASON_STACK1[j-1],
				   min_weight);
  }
  svar = get_satisfied_literal(LINEAR_REASON_STACK2[2]);
  ssign = var_current_value[svar];
  create_ternary_clauses(var, sign, svar, 1-ssign, var2, 1-sign2, min_weight);
  create_ternary_clauses(var, 1-sign, svar, ssign, var2, sign2, min_weight);
  create_ternary_clauses(var, sign, var1, sign1, var2, sign2, min_weight);
  create_ternary_clauses(var, 1-sign, var1, 1-sign1, var2, 1-sign2, min_weight);
  return TRUE;
}

int non_linear_conflict_rs2(int empty_clause,
			    int var1, int sign1,
			    int var2, int sign2,
			    lli_type min_weight) {
	int var, sign, j;
	int svar, ssign;

	var = get_satisfied_literal(LINEAR_REASON_STACK1[3]);
	sign = var_current_value[var];
	for(j = 3; j < LINEAR_REASON_STACK1_fill_pointer - 1; j++) {
		create_complementary_binclause(LINEAR_REASON_STACK1[j],
					       LINEAR_REASON_STACK1[j+1],
					       LINEAR_REASON_STACK1[j-1],
					       min_weight);
	}
	svar = get_satisfied_literal(LINEAR_REASON_STACK1[2]);
	ssign = var_current_value[svar];
	create_ternary_clauses(var, sign, svar, 1-ssign, var1, 1-sign1, min_weight);
	create_ternary_clauses(var, 1-sign, svar, ssign, var1, sign1, min_weight);
	create_ternary_clauses(var, sign, var1, sign1, var2, sign2, min_weight);
	create_ternary_clauses(var, 1-sign, var1, 1-sign1, var2, 1-sign2, min_weight);
	return TRUE;
}

int non_linear_conflict_cub(int empty_clause,
			    int var1, int sign1,
			    int var2, int sign2,
			    lli_type min_weight) {
  int var, sign, j;
  int s1var, s1sign;
  int s2var, s2sign;

  var = get_satisfied_literal(LINEAR_REASON_STACK1[3]);
  sign = var_current_value[var];
  for(j = 3; j < LINEAR_REASON_STACK1_fill_pointer - 1; j++) {
    create_complementary_binclause(LINEAR_REASON_STACK1[j],
				   LINEAR_REASON_STACK1[j+1],
				   LINEAR_REASON_STACK1[j-1],
				   min_weight);
  }
  s1var = get_satisfied_literal(LINEAR_REASON_STACK1[2]);
  s1sign = var_current_value[s1var];
  s2var = get_satisfied_literal(LINEAR_REASON_STACK2[2]);
  s2sign = var_current_value[s2var];
  create_ternary_clauses(var, sign, s1var, 1-s1sign, var1, 1-sign1, min_weight);
  create_ternary_clauses(var, 1-sign, s1var, s1sign, var1, sign1, min_weight);
  create_ternary_clauses(var, sign, s2var, 1-s2sign, var2, 1-sign2, min_weight);
  create_ternary_clauses(var, 1-sign, s2var, s2sign, var2, sign2, min_weight);
  create_ternary_clauses(var, sign, var1, sign1, var2, sign2, min_weight);
  create_ternary_clauses(var, 1-sign, var1, 1-sign1, var2, 1-sign2, min_weight);
  return TRUE;
}

int non_linear_conflict_rs1_3(int empty_clause,
			      int var1, int sign1,
			      int var2, int sign2, lli_type min_weight) {
  int var, sign, j;
  int svar, ssign;
  int s3var, s3sign;

  var = get_satisfied_literal(LINEAR_REASON_STACK1[2]);
  sign = var_current_value[var];
  for(j = 2; j < LINEAR_REASON_STACK1_fill_pointer - 1; j++) {
    create_complementary_binclause(LINEAR_REASON_STACK1[j],
				   LINEAR_REASON_STACK1[j+1],
				   LINEAR_REASON_STACK1[j-1],
				   min_weight);
  }
  svar = get_satisfied_literal(LINEAR_REASON_STACK2[2]);
  ssign = var_current_value[svar];
  s3var = get_satisfied_literal(LINEAR_REASON_STACK2[3]);
  s3sign = var_current_value[s3var];
  create_ternary_clauses(var, sign, s3var, 1-s3sign, svar, ssign, min_weight);
  create_ternary_clauses(var, 1-sign, s3var, s3sign, svar, 1-ssign, min_weight);
  create_ternary_clauses(var, sign, svar, 1-ssign, var2, 1-sign2, min_weight);
  create_ternary_clauses(var, 1-sign, svar, ssign, var2, sign2, min_weight);
  create_ternary_clauses(var, sign, var1, sign1, var2, sign2, min_weight);
  create_ternary_clauses(var, 1-sign, var1, 1-sign1, var2, 1-sign2, min_weight);
  return TRUE;
}

int non_linear_conflict_rs2_3(int empty_clause, int var1, int sign1, int var2, int sign2, lli_type min_weight) {
	int var, sign, j;
	int svar, ssign;
	int s3var, s3sign;

	var = get_satisfied_literal(LINEAR_REASON_STACK1[4]);
	sign = var_current_value[var];
	for(j = 4; j < LINEAR_REASON_STACK1_fill_pointer - 1; j++) {
		create_complementary_binclause(LINEAR_REASON_STACK1[j], LINEAR_REASON_STACK1[j+1], LINEAR_REASON_STACK1[j-1], min_weight);
	}
	svar = get_satisfied_literal(LINEAR_REASON_STACK1[2]);
	ssign = var_current_value[svar];
	s3var = get_satisfied_literal(LINEAR_REASON_STACK1[3]);
	s3sign = var_current_value[s3var];
	create_ternary_clauses(var, sign, s3var, 1-s3sign, svar, ssign, min_weight);
	create_ternary_clauses(var, 1-sign, s3var, s3sign, svar, 1-ssign, min_weight);
	create_ternary_clauses(var, sign, svar, 1-ssign, var1, 1-sign1, min_weight);
	create_ternary_clauses(var, 1-sign, svar, ssign, var1, sign1, min_weight);
	create_ternary_clauses(var, sign, var1, sign1, var2, sign2, min_weight);
	create_ternary_clauses(var, 1-sign, var1, 1-sign1, var2, 1-sign2, min_weight);
	return TRUE;
}

int compute_minweight_for_linear_reasons() {
  int i, min_weight, clause;

  min_weight=clause_weight[LINEAR_REASON_STACK1[0]];
  for(i=1; i<LINEAR_REASON_STACK1_fill_pointer; i++) {
    clause=LINEAR_REASON_STACK1[i];
    if (clause_weight[clause]<min_weight)
      min_weight=clause_weight[clause];
  }
  for(i=0; i<LINEAR_REASON_STACK2_fill_pointer; i++) {
    clause=LINEAR_REASON_STACK2[i];
    if (clause_weight[clause]<min_weight)
      min_weight=clause_weight[clause];
  }
  return min_weight;
}

int linear_conflict(int clause,  lli_type *min_weight) {
  int var, *vars_signs, i=0, varssigns[6], j=0, res, minW;

  vars_signs = var_sign[clause];
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
    if (reason[var]!=NO_REASON) {
      varssigns[i++]=var;
      varssigns[i++]=*(vars_signs+1);
      if (i>4)
	return FALSE;
    }
  }
  if (i>4)
    return FALSE;
  if (i==0) {
    printf("ERROR: Conflict without reason.\n");
    return FALSE;
  } else {
    for(j=0; j<LINEAR_REASON_STACK1_fill_pointer; j++)
      clause_involved[LINEAR_REASON_STACK1[j]]=NONE;
    LINEAR_REASON_STACK1_fill_pointer=1; LINEAR_REASON_STACK2_fill_pointer=1;
    LINEAR_REASON_STACK1[0]=clause; LINEAR_REASON_STACK2[0]=clause;
    if (search_linear_reason1(varssigns[0])==FALSE)
      return FALSE;
    else {
      if (i == 4) {
	res = search_linear_reason2(varssigns[2]);
	if (res == FALSE)
	  return FALSE;
	*min_weight=compute_minweight_for_linear_reasons();
	if (res == SIMPLE_NON_LINEAR_CASE)
	  return non_linear_conflict(clause, varssigns[0], varssigns[1],
				     varssigns[2], varssigns[3], *min_weight);
	else if (res == SIMPLE_RS1_NON_LINEAR_CASE)
	  return non_linear_conflict_rs1(clause, varssigns[0], varssigns[1],
					 varssigns[2], varssigns[3], *min_weight);
	else if (res == SIMPLE_RS2_NON_LINEAR_CASE)
	  return non_linear_conflict_rs2(clause, varssigns[0], varssigns[1],
					 varssigns[2], varssigns[3], *min_weight);
	create_binaryclause(varssigns[0], 1-varssigns[1], varssigns[2],
			    1-varssigns[3], *min_weight);
	for(j = 1; j < LINEAR_REASON_STACK2_fill_pointer - 1; j++) {
	  create_complementary_binclause(LINEAR_REASON_STACK2[j],
					 LINEAR_REASON_STACK2[j+1],
					 LINEAR_REASON_STACK2[j-1], *min_weight);
	}
      }
      if (i==2)
	*min_weight=compute_minweight_for_linear_reasons();
      for(j = 1; j < LINEAR_REASON_STACK1_fill_pointer - 1; j++) {
	create_complementary_binclause(LINEAR_REASON_STACK1[j],
				       LINEAR_REASON_STACK1[j+1],
				       LINEAR_REASON_STACK1[j-1], *min_weight);
      }
    }
    return TRUE;
  }
}

void reduce_clause_weight(int clause, int weight) {
  if (clause_weight[clause] < UB) {
    _push(clause, SAVED_WEIGHTS_CLAUSE);
#ifdef DEBUG
    if (SAVED_WEIGHTS_CLAUSE_fill_pointer > tab_clause_size - 5) {
      printf("DEBUG: SAVED_WEIGHTS_CLAUSE.\n"); exit(0);
    }
#endif
    _push(clause_weight[clause], SAVED_WEIGHTS_WEIGHT);
    clause_weight[clause] -= weight;
  }
}

void remove_linear_reason(int clause, lli_type min_weight) {
  if (clause_weight[clause] == min_weight) {
    clause_state[clause]=PASSIVE;
    _push(clause, CLAUSE_STACK);
  }
  else if (clause_weight[clause] > min_weight) {
    reduce_clause_weight(clause, min_weight);
  }
  else
    printf("ERROR: Negative weight.\n");
  WEIGHTS_TO_REMOVE[CLAUSES_WEIGHTS_TO_REMOVE_fill_pointer]=min_weight;
  _push(clause, CLAUSES_WEIGHTS_TO_REMOVE);
#ifdef DEBUG
  if (CLAUSES_WEIGHTS_TO_REMOVE_fill_pointer > tab_clause_size - 5) {
    printf("DEBUG: CLAUSES_WEIGHTS_TO_REMOVE.\n");
    exit(0);
  }
#endif
}

void remove_linear_reasons(lli_type min_weight) {
  int i, clause;
  for(i = 0; i < LINEAR_REASON_STACK1_fill_pointer; i++) {
    clause = LINEAR_REASON_STACK1[i];
    remove_linear_reason(clause, min_weight);
  }
  for(i = 1; i < LINEAR_REASON_STACK2_fill_pointer; i++) {
    clause=LINEAR_REASON_STACK2[i];
    remove_linear_reason(clause, min_weight);
  }
}

/*
void remove_clauses_for_fl(int var) {
  register int clause,*clauses;
  int p_clause;

  if (var_current_value[var] == POSITIVE)
    clauses =pos_in[var];

  else
      clauses =neg_in[var];
    for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if (clause_state[clause] == ACTIVE) {
      clause_state[clause] = PASSIVE;
      push(clause, CLAUSE_STACK);
    }
  }
}
*/

int my_unitclause_process(int);

int assign_and_unitclause_process( int var, int value, int starting_point) {
  int clause;

  var_current_value[var] = value;
  var_rest_value[var] = NONE;
  var_state[var] = PASSIVE;
  _push(var, VARIABLE_STACK);
  if ((clause = my_reduce_clauses_for_fl(var)) == NO_CONFLICT) {
    //  remove_clauses_for_fl(var);
    return my_unitclause_process(starting_point);
  } else {
    return clause;
  }
}

int clause_involved_in_conflict[tab_clause_size];

int store_reason_clauses( int clause) {
  int *vars_signs, var, i, saved, cl;

  saved=REASON_STACK_fill_pointer;
  _push(clause, REASON_STACK);
  clause_involved_in_conflict[clause]=TRUE;
  for(i = saved;
      i < REASON_STACK_fill_pointer; i++) {
    clause = REASON_STACK[i];
    vars_signs = var_sign[clause];
    for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
      cl=reason[var];
      if (cl!=NO_REASON && clause_involved_in_conflict[cl]==FALSE) {
	_push(cl, REASON_STACK);
	clause_involved_in_conflict[cl]=TRUE;
      }
    }
  }
  for(i=saved; i < REASON_STACK_fill_pointer; i++)
    clause_involved_in_conflict[REASON_STACK[i]]=FALSE;
  return i;
}

void remove_reason_clauses(lli_type *min_weight) {
  int i, clause, minW;
  minW=HARD_WEIGHT;
  for(i = 0; i < REASON_STACK_fill_pointer; i++) {
    clause = REASON_STACK[i];
    if (clause_weight[clause] < minW)
      minW = clause_weight[clause];
  }
  for(i = 0; i < REASON_STACK_fill_pointer; i++) {
    clause = REASON_STACK[i];
    if (clause_weight[clause] <= minW) {
      clause_state[clause] = PASSIVE;
      _push(clause, CLAUSE_STACK);
    }
    else {
      if (clause_weight[clause] < UB) {
	if (clause_entered[clause]==FALSE) {
	  _push(clause, SAVED_WEIGHTS_CLAUSE);
	  clause_entered[clause]=TRUE;
#ifdef DEBUG
	  if (SAVED_WEIGHTS_CLAUSE_fill_pointer > tab_clause_size - 5) {
	    printf("DEBUG: SAVED_WEIGHTS_CLAUSE.\n");
	    exit(0);
	  }
#endif
	  _push(clause_weight[clause], SAVED_WEIGHTS_WEIGHT);
	}
	clause_weight[clause] -= minW;
      }
    }
  }
  *min_weight=minW;
  REASON_STACK_fill_pointer = 0;
}

int search_linear_reason1_for_fl(int falsified_var, int testing_var) {
  int var, *vars_signs, clause, index_var, new_fixed_var,
    testing_var_present, i, a_reason;

  clause=reason[falsified_var];
  vars_signs = var_sign[clause]; new_fixed_var=NONE; testing_var_present=FALSE;
  _push(clause, LINEAR_REASON_STACK1);
  clause_involved[clause]=TRUE;
  for(index_var=*vars_signs; index_var!=NONE; index_var=*(vars_signs+=2)) {
    if (index_var==testing_var)
      testing_var_present=TRUE;
    else if ((index_var!=falsified_var) && (reason[index_var]!=NO_REASON)) {
      if (new_fixed_var==NONE)
	new_fixed_var=index_var;
      else return FALSE;
    }
  }
  if (new_fixed_var==NONE) {
    if (testing_var_present==TRUE)
      return TRUE; //case 1 2, 1 3, -2 -3, testing_var being 1, falsified_var being 2
    else {
      // printf("bizzard...");
      return FALSE;}
  }
  else {
    if (testing_var_present==TRUE)
      // testing_var occurs in a ternary clause such as in 2 -3, 3 5, 2 3 4, -4 -5
      // testing_var being 2, empty_clause being -4 -5, falsified_var is 4
      return FALSE;
    else {
      clause=reason[new_fixed_var];
      clause_involved[clause]=TRUE;
      _push(clause, LINEAR_REASON_STACK1);
      for(i=LINEAR_REASON_STACK1_fill_pointer-1;
	  i<LINEAR_REASON_STACK1_fill_pointer; i++) {
	clause=LINEAR_REASON_STACK1[i];
	vars_signs = var_sign[clause];
	for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
	  a_reason=reason[var];
	  if (a_reason!=NO_REASON && clause_involved[a_reason]!=TRUE) {
	    _push(a_reason, LINEAR_REASON_STACK1);
	    clause_involved[a_reason]=TRUE;
	  }
	}
      }
      return TRUE;
    }
  }
}

int search_linear_reason2_for_fl(int falsified_var, int testing_var) {
  int *vars_signs, clause, index_var, new_fixed_var, testing_var_present;

  clause=reason[falsified_var];
  if (clause==NO_REASON) {
    printf("sdfd..."); return FALSE;}
  if (clause_involved[clause]==TRUE)
    return FALSE;
  _push(clause, LINEAR_REASON_STACK2);
  vars_signs = var_sign[clause]; new_fixed_var=NONE; testing_var_present=FALSE;
  for(index_var=*vars_signs; index_var!=NONE; index_var=*(vars_signs+=2)) {
    if (index_var==testing_var)
      testing_var_present=TRUE;
    else if ((index_var!=falsified_var) && (reason[index_var]!=NO_REASON)) {
      if (new_fixed_var==NONE)
	new_fixed_var=index_var;
      else return FALSE;
    }
  }
  if (new_fixed_var==NONE) {
    if (testing_var_present==TRUE)
      return TRUE; //case 1 2, 1 3, -2 -3, testing_var being 1, falsified_var being 3
    else {
      // printf("bizzard...");
      return FALSE;
    }
  }
  else {
    if (testing_var_present==TRUE)
      // testing_var occurs in a ternary clause such as in 2 -3, 3 4, 2 3 5, -4 -5
      // testing_var being 2, empty_clause being -4 -5, falsified_var is 5
      return FALSE;
    else {
      clause=reason[new_fixed_var];
      if (clause_involved[clause]==TRUE) {
	if ( LINEAR_REASON_STACK2_fill_pointer == 2 &&
	     LINEAR_REASON_STACK1_fill_pointer > 2 &&
	     LINEAR_REASON_STACK1[ 2 ] == clause )
	  return SIMPLE_NON_LINEAR_CASE;
	else
	  return FALSE;
      }
      else return FALSE;
    }
  }
}

// int temp_clause[tab_clause_size];

void cycle_resolution(int var1, int sign1, int var2, int sign2, int var3, int sign3,
		      int clause1, int clause2, int clause3) {
  int unitclause;
  lli_type min_weight;

  min_weight=min(clause_weight[clause1], clause_weight[clause2]);
  min_weight=min(min_weight, clause_weight[clause3]);
  create_ternary_clauses(var1, sign1, var2, sign2, var3, sign3, min_weight);
  unitclause=create_new_unitclause(var1, 1-sign1, min_weight);
  _push(unitclause, CREATED_UNITCLAUSE_STACK);
  _push(unitclause, REASON_STACK);
  create_ternary_clauses(var1, 1-sign1, var2, 1-sign2, var3, 1-sign3, min_weight);
  CLAUSES_TO_REMOVE_fill_pointer=0;
  _push(clause1, CLAUSES_TO_REMOVE);
  _push(clause2, CLAUSES_TO_REMOVE);
  _push(clause3, CLAUSES_TO_REMOVE);
  /*
  if (temp_clause[clause1]==TRUE)
    printf("dsf ");
  if (temp_clause[clause2]==TRUE)
    printf("dsf ");
  if (temp_clause[clause3]==TRUE)
    printf("dsf ");
  */
}

//case 1 2, -2 -3, 1 3 (in this ordering in LINEAR_REASON_STACK1), testing_var being 1
//empty clause is 1 3.
int simple_cycle_case(int testing_var) {
  int var, clause, my_sign, varssigns[4], clause1, clause2,
    i, *vars_signs, unitclause, index_var, new_fixed_var, testing_var_present;
  lli_type  min_weight;

  clause=LINEAR_REASON_STACK1[2];
  vars_signs = var_sign[clause]; new_fixed_var=NONE; testing_var_present=FALSE;
  for(index_var=*vars_signs; index_var!=NONE; index_var=*(vars_signs+=2)) {
    if (index_var==testing_var)
      testing_var_present=TRUE;
    else if (reason[index_var]!=NO_REASON) {
      if (new_fixed_var==NONE)
	new_fixed_var=index_var;
      else return FALSE;
    }
  }
  if ((new_fixed_var==NONE) || (testing_var_present==FALSE))
    return FALSE;
  else {
    clause=LINEAR_REASON_STACK1[1]; my_sign=var_current_value[testing_var];
    vars_signs = var_sign[clause]; i=0;
    for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
      if (reason[var]!=NO_REASON) {
	varssigns[i++]=var; varssigns[i++]=*(vars_signs+1);
	if (i>4)
	  return FALSE;
      }
    }
    if (i!=4)
      return FALSE;
    cycle_resolution(testing_var, my_sign, varssigns[0], varssigns[1],
		     varssigns[2], varssigns[3], clause, LINEAR_REASON_STACK1[0],
		     LINEAR_REASON_STACK1[2]);
    return TRUE;
  }
}

int cycle_conflict(int clause, int testing_var) {
  int var, my_sign, *vars_signs, i=0, varssigns[6], j=0, res, unitclause,
    testing_var_present;
  lli_type  min_weight;
  vars_signs = var_sign[clause]; testing_var_present=FALSE;
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
    if (var==testing_var)
      testing_var_present=TRUE;
    else if (reason[var]!=NO_REASON) {
      varssigns[i++]=var; varssigns[i++]=*(vars_signs+1);
      if (i>4)
	return FALSE;
    }
  }
  if (i==0)
    return FALSE;
  for(j=0; j<LINEAR_REASON_STACK1_fill_pointer; j++)
    clause_involved[LINEAR_REASON_STACK1[j]]=NONE;
  LINEAR_REASON_STACK1_fill_pointer=1; LINEAR_REASON_STACK2_fill_pointer=1;
  LINEAR_REASON_STACK1[0]=clause; LINEAR_REASON_STACK2[0]=clause;
  if (search_linear_reason1_for_fl(varssigns[0], testing_var)==FALSE)
    return FALSE;
  else if ((i==4) && testing_var_present==FALSE) {
    res=search_linear_reason2_for_fl(varssigns[2], testing_var);
    if (res==FALSE)
      return FALSE;
    if ((res==SIMPLE_NON_LINEAR_CASE) ||
	(res==TRUE && LINEAR_REASON_STACK1_fill_pointer == 2 &&
	 LINEAR_REASON_STACK2_fill_pointer == 2)) {
      // SIMPLE_NON_LINEAR_CASE here is such as 1 -2, 2 -3, 3 4, 3 5, -4 -5,
      // testing_var is 1, its value is false, var is 3, its value is false.
      // the other case is 1 2, 1 3, -2 -3, testing var is 1, its value is FALSE
      if (in_conflict[LINEAR_REASON_STACK1[1]]==TRUE ||
	  in_conflict[LINEAR_REASON_STACK2[1]]==TRUE ||
	  in_conflict[clause]==TRUE) {
	//printf("2  ");
	REASON_STACK_fill_pointer=0;
	JOINT_CONFLICT=TRUE;
      }
      if (res==SIMPLE_NON_LINEAR_CASE)
	var=get_satisfied_literal(LINEAR_REASON_STACK1[2]);
      else var=testing_var;
      my_sign=var_current_value[var];
      cycle_resolution(var, my_sign, varssigns[0], varssigns[1],
		       varssigns[2], varssigns[3], clause,
		       LINEAR_REASON_STACK1[1], LINEAR_REASON_STACK2[1]);
      for(j=2; j<LINEAR_REASON_STACK1_fill_pointer; j++)
	_push(LINEAR_REASON_STACK1[j], REASON_STACK);
      return TRUE;
    }
  }
  else if ((i==2) && testing_var_present==TRUE &&
	   LINEAR_REASON_STACK1_fill_pointer == 3) {
    // case 1 2, 1 3, -2 -3, but empty clause is 1 2 or 1 3 and testing_var is 1
    if (simple_cycle_case(testing_var)==TRUE) {
      if (in_conflict[LINEAR_REASON_STACK1[1]]==TRUE) {
	//	printf("1 ");
	REASON_STACK_fill_pointer=0;
	JOINT_CONFLICT=TRUE;
      }
      return TRUE;
    }
    else return FALSE;
  }
  return FALSE;
}

void remove_replaced_clauses() {
  int i, clause1, clause2, clause3;
  lli_type min_weight;

  clause1=CLAUSES_TO_REMOVE[CLAUSES_TO_REMOVE_fill_pointer-3];
  clause2=CLAUSES_TO_REMOVE[CLAUSES_TO_REMOVE_fill_pointer-2];
  clause3=CLAUSES_TO_REMOVE[CLAUSES_TO_REMOVE_fill_pointer-1];
  min_weight=min(clause_weight[clause1], clause_weight[clause2]);
  min_weight=min(min_weight, clause_weight[clause3]);
  remove_linear_reason(clause1, min_weight);
  remove_linear_reason(clause2, min_weight);
  remove_linear_reason(clause3, min_weight);
}

void mark_conflict_clauses() {
  int i, clause;
  for(i=0; i<REASON_STACK_fill_pointer; i++) {
    clause=REASON_STACK[i];
    in_conflict[clause]=TRUE;
    _push(clause, CONFLICTCLAUSE_STACK);
  }
}

void unmark_conflict_clauses() {
  int i;
  for(i=0; i<CONFLICTCLAUSE_STACK_fill_pointer; i++) {
    in_conflict[CONFLICTCLAUSE_STACK[i]]=FALSE;
  }
  CONFLICTCLAUSE_STACK_fill_pointer=0;
}

int CMTR[2];

int test_value(int var, int value, int saved_unitclause_stack_fill_pointer) {
  int my_saved_clause_stack_fill_pointer, saved_reducedclause_stack_fill_pointer,
    my_saved_unitclause_stack_fill_pointer, saved_variable_stack_fill_pointer,
    clause;
  saved_reducedclause_stack_fill_pointer = REDUCEDCLAUSE_STACK_fill_pointer;
  saved_variable_stack_fill_pointer=VARIABLE_STACK_fill_pointer;
  my_saved_clause_stack_fill_pointer= CLAUSE_STACK_fill_pointer;
  my_saved_unitclause_stack_fill_pointer = UNITCLAUSE_STACK_fill_pointer;
  if ((clause=assign_and_unitclause_process(var, value,
					    saved_unitclause_stack_fill_pointer))!=NO_CONFLICT) {
    if (cycle_conflict(clause, var)==TRUE) {
      CMTR[value]++; //printf("sdf...");
      reset_context(my_saved_clause_stack_fill_pointer,
		    saved_reducedclause_stack_fill_pointer,
		    my_saved_unitclause_stack_fill_pointer,
		    saved_variable_stack_fill_pointer);
      remove_replaced_clauses();
      _push(CREATED_UNITCLAUSE_STACK[CREATED_UNITCLAUSE_STACK_fill_pointer-1],
	   UNITCLAUSE_STACK);
    }
    else {
      store_reason_clauses(clause);
      reset_context(my_saved_clause_stack_fill_pointer,
		    saved_reducedclause_stack_fill_pointer,
		    my_saved_unitclause_stack_fill_pointer,
		    saved_variable_stack_fill_pointer);
    }
    return clause;
  }
  else
    reset_context(my_saved_clause_stack_fill_pointer,
		  saved_reducedclause_stack_fill_pointer,
		  my_saved_unitclause_stack_fill_pointer,
		  saved_variable_stack_fill_pointer);
  return NO_CONFLICT;
}

int test_value_fur(int var, int value, int saved_unitclause_stack_fill_pointer) {
  int my_saved_clause_stack_fill_pointer, saved_reducedclause_stack_fill_pointer,
    my_saved_unitclause_stack_fill_pointer, saved_variable_stack_fill_pointer,
    clause;
  saved_reducedclause_stack_fill_pointer = REDUCEDCLAUSE_STACK_fill_pointer;
  saved_variable_stack_fill_pointer=VARIABLE_STACK_fill_pointer;
  my_saved_clause_stack_fill_pointer= CLAUSE_STACK_fill_pointer;
  my_saved_unitclause_stack_fill_pointer = UNITCLAUSE_STACK_fill_pointer;
  if ((clause=assign_and_unitclause_process(var, value,
					    saved_unitclause_stack_fill_pointer))!=NO_CONFLICT) {
      store_reason_clauses(clause);
      reset_context(my_saved_clause_stack_fill_pointer,
		    saved_reducedclause_stack_fill_pointer,
		    my_saved_unitclause_stack_fill_pointer,
		    saved_variable_stack_fill_pointer);
    return clause;
  }
  else
    reset_context(my_saved_clause_stack_fill_pointer,
		  saved_reducedclause_stack_fill_pointer,
		  my_saved_unitclause_stack_fill_pointer,
		  saved_variable_stack_fill_pointer);
  return NO_CONFLICT;
}

int test_value_furth(int var, int value,int saved_unitclause_stack_fill_pointer){
  int my_saved_clause_stack_fill_pointer, saved_reducedclause_stack_fill_pointer,
    my_saved_unitclause_stack_fill_pointer, saved_variable_stack_fill_pointer,
    clause, conflict,saved_reason_stack_pointer;

  saved_reducedclause_stack_fill_pointer = REDUCEDCLAUSE_STACK_fill_pointer;
  saved_variable_stack_fill_pointer=VARIABLE_STACK_fill_pointer;
  my_saved_clause_stack_fill_pointer= CLAUSE_STACK_fill_pointer;
  my_saved_unitclause_stack_fill_pointer = UNITCLAUSE_STACK_fill_pointer;
  saved_reason_stack_pointer=REASON_STACK_fill_pointer;
  if ((clause=assign_and_unitclause_process(var, value,
		         saved_unitclause_stack_fill_pointer))!=NO_CONFLICT) {
     store_reason_clauses(clause);
     reset_context(my_saved_clause_stack_fill_pointer,
			      saved_reducedclause_stack_fill_pointer,
			      my_saved_unitclause_stack_fill_pointer,
			      saved_variable_stack_fill_pointer);
    return TRUE;
  }
  else {
    for( var=0; var< NB_VAR; var++ ) {
      if ( var_state[ var ] == ACTIVE) {
	if (nb_neg_clause_of_length2[ var ] > 0 &&
	    nb_pos_clause_of_length2[ var ] > 0 ) {
	  if (nb_neg_clause_of_length2[ var ]<nb_pos_clause_of_length2[ var ])
	    value=TRUE;
	  else value=FALSE;
	  REASON_STACK_fill_pointer=saved_reason_stack_pointer;
	  if (test_value_fur(var, value,
			 saved_unitclause_stack_fill_pointer)!=NO_CONFLICT){
	    if (test_value_fur(var, 1-value,
			   saved_unitclause_stack_fill_pointer)!=NO_CONFLICT) {
	     reset_context(my_saved_clause_stack_fill_pointer,
		saved_reducedclause_stack_fill_pointer,
		my_saved_unitclause_stack_fill_pointer,
		saved_variable_stack_fill_pointer);
	      return TRUE;
	    }
	  }
	}
      }
    }
  }
  reset_context(my_saved_clause_stack_fill_pointer,
		saved_reducedclause_stack_fill_pointer,
		my_saved_unitclause_stack_fill_pointer,
		saved_variable_stack_fill_pointer);
  return NO_CONFLICT;
}


int fur_lookahead_fl(int saved_unitclause_stack_fill_pointer,lli_type conflicts){
 int var,value;
 lli_type min_weight;
 int  saved_reducedclause_stack_fill_pointer,saved_variable_stack_fill_pointer,
    my_saved_clause_stack_fill_pointer, my_saved_unitclause_stack_fill_pointer, saved;
  saved_reducedclause_stack_fill_pointer = REDUCEDCLAUSE_STACK_fill_pointer;
  saved_variable_stack_fill_pointer=VARIABLE_STACK_fill_pointer;
  my_saved_clause_stack_fill_pointer= CLAUSE_STACK_fill_pointer;
  my_saved_unitclause_stack_fill_pointer = UNITCLAUSE_STACK_fill_pointer;

 for( var=0; var < NB_VAR&&conflicts+NB_EMPTY<UB; var++ ) {
    if (var_state[var] == ACTIVE) {
      simple_get_pos_clause_nb(var); simple_get_neg_clause_nb(var);
      if (nb_neg_clause_of_length2[var] > 0 &&
          nb_pos_clause_of_length2[var] > 0 ) {
	 if (nb_neg_clause_of_length2[var]<nb_pos_clause_of_length2[var])
	     value=TRUE;
	 else value=FALSE;
	 REASON_STACK_fill_pointer=0;
        if (test_value(var, value,
		       saved_unitclause_stack_fill_pointer)!=NO_CONFLICT) {
	   if (test_value_furth(var, 1-value,
			saved_unitclause_stack_fill_pointer)==TRUE){
             remove_reason_clauses(&min_weight);
          	conflicts+=min_weight;
	   }
        }
      }
    }
 }
 reset_context(my_saved_clause_stack_fill_pointer,
			      saved_reducedclause_stack_fill_pointer,
			      my_saved_unitclause_stack_fill_pointer,
			      saved_variable_stack_fill_pointer);
 return conflicts;
}


int lookahead_by_fl( lli_type nb_known_conflicts ) {
  int clause, var, i, value;
  int saved_clause_stack_fill_pointer, saved_reducedclause_stack_fill_pointer,
    saved_unitclause_stack_fill_pointer, saved_variable_stack_fill_pointer,
    my_saved_clause_stack_fill_pointer, saved_reason_stack_fill_pointer,
    my_saved_unitclause_stack_fill_pointer, saved;
  lli_type nb_conflicts, min_weight;
   int flag=FALSE;
  // saved=REDUCEDCLAUSE_STACK_fill_pointer;
 // if (my_unitclause_process(0)!=NO_CONFLICT)
 //   printf("sdfsd\n");
  // for(i=saved; i<REDUCEDCLAUSE_STACK_fill_pointer; i++)
  //  temp_clause[REDUCEDCLAUSE_STACK[i]]=TRUE;
  nb_conflicts=nb_known_conflicts;
  saved_clause_stack_fill_pointer= CLAUSE_STACK_fill_pointer;
  saved_reducedclause_stack_fill_pointer = REDUCEDCLAUSE_STACK_fill_pointer;
  saved_unitclause_stack_fill_pointer = UNITCLAUSE_STACK_fill_pointer;
  saved_variable_stack_fill_pointer=VARIABLE_STACK_fill_pointer;
  my_saved_clause_stack_fill_pointer= CLAUSE_STACK_fill_pointer;
  my_saved_unitclause_stack_fill_pointer = UNITCLAUSE_STACK_fill_pointer;

  //~ zz_print_structure();
  for( var=0; var < NB_VAR && nb_conflicts+NB_EMPTY<UB; var++ ) {
     if(flag==FALSE){
         if ((clause=my_unitclause_process(0))!=NO_CONFLICT){
//           printf("sdfsd\n");
	    REASON_STACK_fill_pointer=0;
	    store_reason_clauses(clause);
	    remove_reason_clauses(&min_weight);
//	    my_saved_unitclause_stack_fill_pointer = UNITCLAUSE_STACK_fill_pointer;
	    my_saved_clause_stack_fill_pointer=CLAUSE_STACK_fill_pointer;
	    nb_conflicts+=min_weight;
	    flag=FALSE; var--;
	    reset_context(my_saved_clause_stack_fill_pointer,
			      saved_reducedclause_stack_fill_pointer,
			      my_saved_unitclause_stack_fill_pointer,
			      saved_variable_stack_fill_pointer);
	    continue;
           }
	}
    if ( var_state[ var ] == ACTIVE) { // && avoid[var]==FALSE) {
       simple_get_pos_clause_nb(var); simple_get_neg_clause_nb(var);
       if (nb_neg_clause_of_length2[ var ] > 1 &&
          nb_pos_clause_of_length2[ var ] > 1 ) {
	if (nb_neg_clause_of_length2[ var ]<nb_pos_clause_of_length2[ var ])
	  value=TRUE;
	else value=FALSE;
        REASON_STACK_fill_pointer = 0; unmark_conflict_clauses();
	JOINT_CONFLICT=FALSE;
        if (test_value(var, value,
		       my_saved_unitclause_stack_fill_pointer)!=NO_CONFLICT) {
	  mark_conflict_clauses();
	  if (test_value(var, 1-value,
			 my_saved_unitclause_stack_fill_pointer)!=NO_CONFLICT) {
	    if (JOINT_CONFLICT==TRUE) {
	      my_saved_unitclause_stack_fill_pointer = UNITCLAUSE_STACK_fill_pointer;
	      my_saved_clause_stack_fill_pointer=CLAUSE_STACK_fill_pointer;
	      if ((clause=assign_and_unitclause_process(var, value,
			      my_saved_unitclause_stack_fill_pointer))!=NO_CONFLICT) {
		store_reason_clauses(clause);
		reset_context(my_saved_clause_stack_fill_pointer,
			      saved_reducedclause_stack_fill_pointer,
			      my_saved_unitclause_stack_fill_pointer,
			      saved_variable_stack_fill_pointer);
		remove_reason_clauses(&min_weight);
		my_saved_clause_stack_fill_pointer=CLAUSE_STACK_fill_pointer;
		nb_conflicts+=min_weight;
	      }
		reset_context(my_saved_clause_stack_fill_pointer,
			      saved_reducedclause_stack_fill_pointer,
			      my_saved_unitclause_stack_fill_pointer,
			      saved_variable_stack_fill_pointer);
	    }
	    else {
	      remove_reason_clauses(&min_weight);
	      my_saved_unitclause_stack_fill_pointer = UNITCLAUSE_STACK_fill_pointer;
	      my_saved_clause_stack_fill_pointer=CLAUSE_STACK_fill_pointer;
	      reset_context(my_saved_clause_stack_fill_pointer,
			      saved_reducedclause_stack_fill_pointer,
			      my_saved_unitclause_stack_fill_pointer,
			      saved_variable_stack_fill_pointer);
	      nb_conflicts+=min_weight;
	    }
	      flag=FALSE;continue;
          }
	  //x1=1 conflict, x1=0 no conflict
	  my_saved_unitclause_stack_fill_pointer = UNITCLAUSE_STACK_fill_pointer;
	  my_saved_clause_stack_fill_pointer=CLAUSE_STACK_fill_pointer;
	  flag=TRUE;continue;
	}
//       flag=TRUE; //x1=1 NO CONFLICT
      }
    }
    flag=TRUE;
  }
  reset_context(my_saved_clause_stack_fill_pointer,
			      saved_reducedclause_stack_fill_pointer,
			      my_saved_unitclause_stack_fill_pointer,
			      saved_variable_stack_fill_pointer);

  if(instance_length==TRUE){
    if(instance_type==1&&partial==0&&nb_conflicts+NB_EMPTY<UB)
	nb_conflicts=fur_lookahead_fl(my_saved_unitclause_stack_fill_pointer,nb_conflicts);
    else
	if(UB-nb_conflicts-NB_EMPTY==1)
	  nb_conflicts=fur_lookahead_fl(my_saved_unitclause_stack_fill_pointer,nb_conflicts);
  }

  reset_context(saved_clause_stack_fill_pointer,
                saved_reducedclause_stack_fill_pointer,
                saved_unitclause_stack_fill_pointer,
                saved_variable_stack_fill_pointer);
//  zz_print_structure();
  //  for(i=saved; i<saved_reducedclause_stack_fill_pointer; i++)
  //  temp_clause[REDUCEDCLAUSE_STACK[i]]=FALSE;
  return nb_conflicts;
}
int search_linear_reason1_for_up(int falsified_var) {
  int var, *vars_signs, clause, index_var, new_fixed_var, i, a_reason;

  clause=reason[falsified_var];
  vars_signs = var_sign[clause]; new_fixed_var=NONE;
  _push(clause, LINEAR_REASON_STACK1);
  clause_involved[clause]=TRUE;
  for(index_var=*vars_signs; index_var!=NONE; index_var=*(vars_signs+=2)) {
    if ((index_var!=falsified_var) && (reason[index_var]!=NO_REASON)) {
      if (new_fixed_var==NONE)
	new_fixed_var=index_var;
      else return FALSE;
    }
  }
  if (new_fixed_var==NONE)
    return FALSE;
  clause=reason[new_fixed_var];
  clause_involved[clause]=TRUE;
  _push(clause, LINEAR_REASON_STACK1);
  for(i=LINEAR_REASON_STACK1_fill_pointer-1;
      i<LINEAR_REASON_STACK1_fill_pointer; i++) {
    clause=LINEAR_REASON_STACK1[i];
    vars_signs = var_sign[clause];
    for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
      a_reason=reason[var];
      if (a_reason!=NO_REASON && clause_involved[a_reason]!=TRUE) {
	_push(a_reason, LINEAR_REASON_STACK1);
	clause_involved[a_reason]=TRUE;
      }
    }
  }
  return TRUE;
}

int search_linear_reason2_for_up(int falsified_var) {
  int *vars_signs, clause, index_var, new_fixed_var;

  clause=reason[falsified_var];
  if (clause==NO_REASON) {
    printf("sdfd..."); return FALSE;}
  if (clause_involved[clause]==TRUE)
    return FALSE;
  _push(clause, LINEAR_REASON_STACK2);
  vars_signs = var_sign[clause]; new_fixed_var=NONE;
  for(index_var=*vars_signs; index_var!=NONE; index_var=*(vars_signs+=2)) {
    if ((index_var!=falsified_var) && (reason[index_var]!=NO_REASON)) {
      if (new_fixed_var==NONE)
	new_fixed_var=index_var;
      else return FALSE;
    }
  }
  if (new_fixed_var==NONE)
    return FALSE;
  clause=reason[new_fixed_var];
  if (clause_involved[clause]==TRUE) {
    if ( LINEAR_REASON_STACK2_fill_pointer == 2 &&
	 LINEAR_REASON_STACK1_fill_pointer > 2 &&
	 LINEAR_REASON_STACK1[ 2 ] == clause )
      return SIMPLE_NON_LINEAR_CASE;
    else
      return FALSE;
  }
  else return FALSE;
}

int cycle_conflict_by_up(int clause) {
  int var, my_sign, *vars_signs, i=0, varssigns[6], j=0, res, unitclause;
  lli_type  min_weight;
  vars_signs = var_sign[clause];
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
    if (reason[var]!=NO_REASON) {
      varssigns[i++]=var; varssigns[i++]=*(vars_signs+1);
      if (i>4)
	return FALSE;
    }
  }
  if (i==0)
    return FALSE;
  for(j=0; j<LINEAR_REASON_STACK1_fill_pointer; j++)
    clause_involved[LINEAR_REASON_STACK1[j]]=NONE;
  LINEAR_REASON_STACK1_fill_pointer=1; LINEAR_REASON_STACK2_fill_pointer=1;
  LINEAR_REASON_STACK1[0]=clause; LINEAR_REASON_STACK2[0]=clause;
  if (search_linear_reason1_for_up(varssigns[0])==FALSE)
    return FALSE;
  else if (i==4) {
    res=search_linear_reason2_for_up(varssigns[2]);
    if (res==FALSE)
      return FALSE;
    if (res==SIMPLE_NON_LINEAR_CASE) {
      // SIMPLE_NON_LINEAR_CASE here is such as 1 -2, 2 -3, 3 4, 3 5, -4 -5,
      REASON_STACK_fill_pointer=0;
      var=get_satisfied_literal(LINEAR_REASON_STACK1[2]);
      my_sign=var_current_value[var];
      cycle_resolution(var, my_sign, varssigns[0], varssigns[1],
		       varssigns[2], varssigns[3], clause,
		       LINEAR_REASON_STACK1[1], LINEAR_REASON_STACK2[1]);
      for(j=2; j<LINEAR_REASON_STACK1_fill_pointer; j++)
	_push(LINEAR_REASON_STACK1[j], REASON_STACK);
      return TRUE;
    }
  }
  return FALSE;
}

int binclause_reducing_reason[tab_clause_size];
int SAVEDCLAUSE;
#define NO_APPLY -2

int my_reduce_clauses_for_ir(int var) {
  register int clause, *clauses;
  int nb, *vars_signs, varssigns[2], a_var;

  if (var_current_value[var] == POSITIVE)
    clauses =neg_in[var];
  else clauses =pos_in[var];
  for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if (clause_state[clause] == ACTIVE) {
      switch (clause_length[clause]) {
      case 1:
	clause_length[clause]--;
	_push(clause, MY_UNITCLAUSE_STACK);
	if (binclause_reducing_reason[clause]==NONE) {
	  if (SAVEDCLAUSE==NO_APPLY)
	    SAVEDCLAUSE=clause;
#if DEBUG
	  vars_signs = var_sign[clause]; nb=0;
	  for(a_var=*vars_signs; a_var!=NONE; a_var=*(vars_signs+=2)) {
	    if (reason[a_var] != NO_REASON &&
		var_current_value[a_var]!=*(vars_signs+1)) {
	      varssigns[nb++]=a_var;
	      if (nb>2)
		printf("sdfsdq1 ");
	    }
	  }
	  if (nb!=1)
	    printf("xcdfqsfq ");
#endif
	}
	else {
	  vars_signs = var_sign[clause]; nb=0;
	  for(a_var=*vars_signs; a_var!=NONE; a_var=*(vars_signs+=2)) {
	    if (reason[a_var] != NO_REASON &&
		var_current_value[a_var]!=*(vars_signs+1)) {
	      varssigns[nb++]=a_var;
	      if (nb>2)
		printf("sdfsdq1 ");
	    }
	  }
	  if (nb!=2) // && nb!=0)
	    printf("sdfsdq2 ");
	  //  if (nb==2)
	    if (binclause_reducing_reason[reason[varssigns[0]]]==
		binclause_reducing_reason[reason[varssigns[1]]])
	      return clause;
	  break;
	}
      case 2:  clause_length[clause]--;
	binclause_reducing_reason[clause]=var;
	_push(clause, MY_UNITCLAUSE_STACK);
	break;
      }
    }
  }
  return SAVEDCLAUSE;
}

int satisfy_unitclause_for_ir(int unitclause) {
  int *vars_signs, var, clause;

  vars_signs = var_sign[unitclause];
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
    if (var_state[var] == ACTIVE ) {
      var_current_value[var] = *(vars_signs+1);
      var_rest_value[var] = NONE;
      reason[var]=unitclause;
      var_state[var] = PASSIVE;
      _push(var, VARIABLE_STACK);
      // remove_clauses(var);
      if ((clause=my_reduce_clauses_for_ir(var))!=NO_APPLY) {
	return clause;
      }
      break;
    }
  }
  return NO_APPLY;
}

int get_applicable_empty_clause(int unitclause) {
  int my_unitclause_position, my_unitclause, clause, i;

  MY_UNITCLAUSE_STACK_fill_pointer = 0; SAVEDCLAUSE=NO_APPLY;
  clause=NO_APPLY;
  if ((clause=satisfy_unitclause_for_ir(unitclause))==NO_APPLY) {
    for (i=0; i<MY_UNITCLAUSE_STACK_fill_pointer; i++) {
      my_unitclause = MY_UNITCLAUSE_STACK[i];
      if ((clause_state[my_unitclause] == ACTIVE) &&
	  (clause_length[my_unitclause]>0)) {
	if ((clause=satisfy_unitclause_for_ir(my_unitclause)) != NO_APPLY)
	  break;
      }
    }
  }
  for(i=0; i<MY_UNITCLAUSE_STACK_fill_pointer; i++) {
    binclause_reducing_reason[MY_UNITCLAUSE_STACK[i]]=NONE;
    clause_length[MY_UNITCLAUSE_STACK[i]]++;
  }
  MY_UNITCLAUSE_STACK_fill_pointer=0;
  return clause;
}

int apply_ir() {
  int saved_reducedclause_stack_fill_pointer, saved_unitclause_stack_fill_pointer,
    saved_variable_stack_fill_pointer, my_saved_clause_stack_fill_pointer,
    i, clause, my_saved_unitclause_stack_fill_pointer, unitclause;
  lli_type min_weight;
  saved_reducedclause_stack_fill_pointer = REDUCEDCLAUSE_STACK_fill_pointer;
  saved_unitclause_stack_fill_pointer = UNITCLAUSE_STACK_fill_pointer;
  saved_variable_stack_fill_pointer=VARIABLE_STACK_fill_pointer;
  my_saved_clause_stack_fill_pointer= CLAUSE_STACK_fill_pointer;
  my_saved_unitclause_stack_fill_pointer=UNITCLAUSE_STACK_fill_pointer;
  for (i = 0; i < UNITCLAUSE_STACK_fill_pointer; i++) {
    unitclause = UNITCLAUSE_STACK[i];
    if ((clause_state[unitclause] == ACTIVE)
	&& (clause_length[unitclause]>0)) {
      if ((clause=get_applicable_empty_clause(unitclause))!=NO_APPLY &&
	  (linear_conflict(clause, &min_weight)==TRUE)) {
	NB_EMPTY += min_weight;
	reset_context(my_saved_clause_stack_fill_pointer,
		      saved_reducedclause_stack_fill_pointer,
		      my_saved_unitclause_stack_fill_pointer,
		      saved_variable_stack_fill_pointer);
	remove_linear_reasons(min_weight);
	my_saved_clause_stack_fill_pointer=CLAUSE_STACK_fill_pointer;
	if (NB_EMPTY>=UB)
	  break;
      }
      else {
	if (clause != NO_APPLY)
	  printf("bizzar...."); // ????
	reset_context(my_saved_clause_stack_fill_pointer,
		      saved_reducedclause_stack_fill_pointer,
		      my_saved_unitclause_stack_fill_pointer,
		      saved_variable_stack_fill_pointer);
      }
    }
  }
  reset_context(my_saved_clause_stack_fill_pointer,
		saved_reducedclause_stack_fill_pointer,
		my_saved_unitclause_stack_fill_pointer,
		saved_variable_stack_fill_pointer);
  return NB_EMPTY;
}

int lookahead_by_up(lli_type nb_known_conflicts) {
  int saved_reducedclause_stack_fill_pointer, saved_unitclause_stack_fill_pointer,
    saved_variable_stack_fill_pointer, my_saved_clause_stack_fill_pointer,
    clause, i, var, *vars_signs, my_saved_unitclause_stack_fill_pointer;
  lli_type nb_conflicts, min_weight;
  nb_conflicts=nb_known_conflicts;
  saved_reducedclause_stack_fill_pointer = REDUCEDCLAUSE_STACK_fill_pointer;
  saved_unitclause_stack_fill_pointer = UNITCLAUSE_STACK_fill_pointer;
  saved_variable_stack_fill_pointer=VARIABLE_STACK_fill_pointer;
  my_saved_clause_stack_fill_pointer= CLAUSE_STACK_fill_pointer;
  my_saved_unitclause_stack_fill_pointer=UNITCLAUSE_STACK_fill_pointer;
  while ((clause=my_unitclause_process(0))!=NO_CONFLICT) {
    if (linear_conflict(clause, &min_weight)==TRUE) {
      NB_EMPTY += min_weight;
      reset_context(my_saved_clause_stack_fill_pointer,
		    saved_reducedclause_stack_fill_pointer,
		    my_saved_unitclause_stack_fill_pointer,
		    saved_variable_stack_fill_pointer);
      remove_linear_reasons(min_weight);
      my_saved_clause_stack_fill_pointer=CLAUSE_STACK_fill_pointer;
    }
    else if (cycle_conflict_by_up(clause)==TRUE) {
      reset_context(my_saved_clause_stack_fill_pointer,
		    saved_reducedclause_stack_fill_pointer,
		    my_saved_unitclause_stack_fill_pointer,
		    saved_variable_stack_fill_pointer);
      remove_replaced_clauses();
      _push(CREATED_UNITCLAUSE_STACK[CREATED_UNITCLAUSE_STACK_fill_pointer-1],
	   UNITCLAUSE_STACK);
      remove_reason_clauses(&min_weight);
      my_saved_clause_stack_fill_pointer=CLAUSE_STACK_fill_pointer;
      my_saved_unitclause_stack_fill_pointer=UNITCLAUSE_STACK_fill_pointer;
      nb_conflicts+=min_weight;
    }
    else {
      REASON_STACK_fill_pointer=0; store_reason_clauses(clause);
      reset_context(my_saved_clause_stack_fill_pointer,
		    saved_reducedclause_stack_fill_pointer,
		    my_saved_unitclause_stack_fill_pointer,
		    saved_variable_stack_fill_pointer);
      remove_reason_clauses(&min_weight);
      my_saved_clause_stack_fill_pointer=CLAUSE_STACK_fill_pointer;
      nb_conflicts+=min_weight;
    }
    if (nb_conflicts+NB_EMPTY>=UB)
      break;
  }
  //  mark_variables(saved_variable_stack_fill_pointer);
  reset_context(my_saved_clause_stack_fill_pointer,
		saved_reducedclause_stack_fill_pointer,
		my_saved_unitclause_stack_fill_pointer,
		saved_variable_stack_fill_pointer);
  return nb_conflicts;
}

void remove_premiss_clauses_weight() {
  int i, clause;
  for (i = 0; i < CLAUSES_WEIGHTS_TO_REMOVE_fill_pointer; i++) {
    clause = CLAUSES_WEIGHTS_TO_REMOVE[i];
    if (clause_weight[clause] == WEIGHTS_TO_REMOVE[i]) {
      _push(clause, CLAUSE_STACK);
      clause_state[clause]=PASSIVE;
    }
    else
      reduce_clause_weight(clause, WEIGHTS_TO_REMOVE[i]);
  }
  CLAUSES_WEIGHTS_TO_REMOVE_fill_pointer = 0;
}

void reset_clause_weight(int saved_clause_weight_stack_fill_pointer) {
  int clause, i;
  for (i = SAVED_WEIGHTS_CLAUSE_fill_pointer - 1;
       i >= saved_clause_weight_stack_fill_pointer; i--) {
    clause=SAVED_WEIGHTS_CLAUSE[i];     clause_entered[clause]=FALSE;
    clause_weight[clause] = SAVED_WEIGHTS_WEIGHT[i];
  }
  SAVED_WEIGHTS_CLAUSE_fill_pointer = saved_clause_weight_stack_fill_pointer;
  SAVED_WEIGHTS_WEIGHT_fill_pointer = saved_clause_weight_stack_fill_pointer;
}

int lookahead() {
  int saved_clause_stack_fill_pointer, saved_reducedclause_stack_fill_pointer,
    saved_unitclause_stack_fill_pointer, saved_variable_stack_fill_pointer,
    my_saved_clause_stack_fill_pointer,  saved_clause_weight_stack_fill_pointer,
    clause, i;
  lli_type conflict=0;

  CLAUSES_WEIGHTS_TO_REMOVE_fill_pointer = 0;
  CREATED_UNITCLAUSE_STACK_fill_pointer=0;
  saved_clause_stack_fill_pointer= CLAUSE_STACK_fill_pointer;
  saved_reducedclause_stack_fill_pointer = REDUCEDCLAUSE_STACK_fill_pointer;
  saved_unitclause_stack_fill_pointer = UNITCLAUSE_STACK_fill_pointer;
  saved_variable_stack_fill_pointer=VARIABLE_STACK_fill_pointer;
  saved_clause_weight_stack_fill_pointer=SAVED_WEIGHTS_CLAUSE_fill_pointer;
  if(instance_length==FALSE&&instance_type==1)
  	conflict=0;
  else
     apply_ir();
  if (NB_EMPTY<UB) {
    conflict=lookahead_by_up(0);
    if (conflict+NB_EMPTY<UB) {
      conflict = lookahead_by_fl(conflict);
      if (conflict+NB_EMPTY<UB) {
	reset_context(saved_clause_stack_fill_pointer,
		      saved_reducedclause_stack_fill_pointer,
		      saved_unitclause_stack_fill_pointer,
		      saved_variable_stack_fill_pointer);
	reset_clause_weight(saved_clause_weight_stack_fill_pointer);
	remove_premiss_clauses_weight();
	for(i=0; i<CREATED_UNITCLAUSE_STACK_fill_pointer; i++)
	  _push(CREATED_UNITCLAUSE_STACK[i], UNITCLAUSE_STACK);
	CREATED_UNITCLAUSE_STACK_fill_pointer=0;
	return conflict;
      }
    }
  }
  reset_context(saved_clause_stack_fill_pointer,
		saved_reducedclause_stack_fill_pointer,
		saved_unitclause_stack_fill_pointer,
		saved_variable_stack_fill_pointer);
  reset_clause_weight(saved_clause_weight_stack_fill_pointer);
  return NONE;
}

int satisfy_unitclause(int unitclause) {
  int *vars_signs, var, clause;

  vars_signs = var_sign[unitclause];
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
    if (var_state[var] == ACTIVE ){
      var_current_value[var] = *(vars_signs+1);
      var_rest_value[var] = NONE;
      reason[var]=unitclause;
      var_state[var] = PASSIVE;
      _push(var, VARIABLE_STACK);
      if ((clause=my_reduce_clauses(var))==NO_CONFLICT) {
	//	remove_clauses(var);
	return NO_CONFLICT;
      } else
	return clause;
    }
  }
  return NO_CONFLICT;
}

int my_unitclause_process(int starting_point) {
  int unitclause, unitclause_position,clause,
    my_unitclause_position, my_unitclause;

  for (unitclause_position = starting_point;
       unitclause_position < UNITCLAUSE_STACK_fill_pointer;
       unitclause_position++) {
    unitclause = UNITCLAUSE_STACK[unitclause_position];
    if ((clause_state[unitclause] == ACTIVE)
	&& (clause_length[unitclause]>0)
	/*&& unitclause > INIT_BASE_NB_CLAUSE*/) {
      MY_UNITCLAUSE_STACK_fill_pointer = 0;
      if ((clause=satisfy_unitclause(unitclause)) != NO_CONFLICT) {
	return clause;
      } else {
	for (my_unitclause_position = 0;
	     my_unitclause_position < MY_UNITCLAUSE_STACK_fill_pointer;
	     my_unitclause_position++) {
	  my_unitclause = MY_UNITCLAUSE_STACK[my_unitclause_position];
	  if ((clause_state[my_unitclause] == ACTIVE) &&
	      (clause_length[my_unitclause]>0)
	      /*&& my_unitclause > INIT_BASE_NB_CLAUSE*/) {
	    if ((clause=satisfy_unitclause(my_unitclause)) != NO_CONFLICT) {
	      return clause;
	    }
	  }
	}
      }
    }
  }
  return NO_CONFLICT;
}

int get_complement(int lit) {
  if (positive(lit))
    return lit+NB_VAR;
  else
    return lit-NB_VAR;
}

void create_unitclause(int lit, int subsumedclause, lli_type weight) {
  int clause, *vars_signs, flag=FALSE, *clauses, var, sign;

  vars_signs=NEW_CLAUSES[NEW_CLAUSES_fill_pointer++];
  if (lit<NB_VAR) {
	var= lit; vars_signs[0]=var; vars_signs[1]=POSITIVE, sign= POSITIVE;
  } else {
    var= lit-NB_VAR; vars_signs[0]=var; vars_signs[1]=NEGATIVE, sign= NEGATIVE;
  }
  vars_signs[2]=NONE;
  var_sign[NB_CLAUSE]=vars_signs;
  clause_state[NB_CLAUSE]=ACTIVE;
  clause_length[NB_CLAUSE] = 1;
  clause_weight[NB_CLAUSE] = weight;
  _push(NB_CLAUSE, UNITCLAUSE_STACK);

  add_newclause_in(var,sign);

  NB_CLAUSE++;
#ifdef DEBUG
  if (NB_CLAUSE > tab_clause_size - 5) {
    printf("DEBUG: NB_CLAUSE.\n");
    exit(0);
  }
#endif
}

void verify_resolvent(int lit, int clause1, int clause2) {
  int *vars_signs1, *vars_signs2, lit1=NONE, lit2=NONE,
    temp, flag=FALSE, var, nb=0;

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
      if (temp==lit)
	flag=TRUE;
      else
	lit1=temp;
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
      else
	temp=var+NB_VAR;
      if (temp==lit)
	flag=TRUE;
      else
	lit2=temp;
    }
  }
  if ((nb!=2) || (flag==FALSE))
    printf("erreur ");
  if (!complement(lit1, lit2))
    printf("erreur ");
}

lli_type simple_get_neg_clause_nb(int var) {
  lli_type neg_clause2_nb = 0;
  int p_clause, clause, *clauses;

  clauses =neg_in[var];
  for(clause=*clauses; clause!=NONE; clause=*(++clauses))
    if ((clause_state[clause] == ACTIVE) && (clause_length[clause]==2))
      neg_clause2_nb += clause_weight[clause];
      nb_neg_clause_of_length2[var] = neg_clause2_nb;
  return neg_clause2_nb;
}

lli_type simple_get_pos_clause_nb(int var) {
  lli_type pos_clause2_nb = 0;
  int p_clause, clause, *clauses;
  clauses = pos_in[var];

  for(clause=*clauses; clause!=NONE; clause=*(++clauses))
    if ((clause_state[clause] == ACTIVE) && (clause_length[clause]==2))
      pos_clause2_nb += clause_weight[clause];
  nb_pos_clause_of_length2[var] = pos_clause2_nb;
  return pos_clause2_nb;
}

int in_clause_neg[2*tab_variable_size];
int in_clause_pos[2*tab_variable_size];
int literal_clause_stack[tab_clause_size];
int literal_clause_stack_fill_pointer=0;
int marked_literals_stack[2*tab_variable_size];
int marked_literals_stack_fill_pointer=0;
int marked_literals2_stack[2*tab_variable_size];
int marked_literals2_stack_fill_pointer=0;

void insert_clause(int lit, int clause) {
  if (in_clause_neg[lit]==NONE)
    _push(lit, marked_literals_stack);
  literal_clause_stack[literal_clause_stack_fill_pointer]=clause;
  literal_clause_stack[literal_clause_stack_fill_pointer+1]= in_clause_neg[lit];
  in_clause_neg[lit]=literal_clause_stack_fill_pointer;
  literal_clause_stack_fill_pointer=literal_clause_stack_fill_pointer+2;
}

void merge_clause(int clause1, int clause2) {
  clause_state[clause2] = PASSIVE; _push(clause2, CLAUSE_STACK);
  reduce_clause_weight(clause1, -clause_weight[clause2]);
}

void mark_literals(int var) {
  int *vars_signs, i, clause, index_var, lit,*clauses;
  for(i=0; i<marked_literals_stack_fill_pointer; i++)
    in_clause_neg[marked_literals_stack[i]]=NONE;
  marked_literals_stack_fill_pointer=0;
  MY_UNITCLAUSE_STACK_fill_pointer=0;
  clauses =neg_in[var];

  for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if (clause_state[clause] == ACTIVE) {
      if (clause_length[clause]==2) {
	vars_signs = var_sign[clause];
	for(index_var=*vars_signs; index_var!=NONE; index_var=*(vars_signs+=2)) {
	  if (var_state[index_var]==ACTIVE && index_var != var) {
	    if (*(vars_signs+1) ==TRUE) lit=index_var; else lit=index_var+NB_VAR;
	    if (in_clause_neg[lit] ==NONE) {
	      _push(lit, marked_literals_stack);
	      in_clause_neg[lit]=clause;
	    }
	    else
	      merge_clause(in_clause_neg[lit], clause);
	    break;
	  }
	}
      }
      else if (clause_length[clause]==1)
	_push(clause, MY_UNITCLAUSE_STACK);
    }
  }
}

void treat_binary_clauses(int lit, int clause1, int clause2) {
  int sign;

  if (lit<NB_VAR) sign =POSITIVE;
  else  sign =NEGATIVE;
  if (clause_weight[clause2] > clause_weight[clause1]) {
    clause_state[clause1] = PASSIVE; _push(clause1, CLAUSE_STACK);
    create_unitclause(lit, clause1, clause_weight[clause1]);
    reduce_clause_weight(clause2, clause_weight[clause1]);
  }
  else if (clause_weight[clause2] == clause_weight[clause1]) {
    clause_state[clause1] = PASSIVE; _push(clause1, CLAUSE_STACK);
    clause_state[clause2] = PASSIVE; _push(clause2, CLAUSE_STACK);
    create_unitclause(lit, clause1, clause_weight[clause1]);
  }
  else {
    clause_state[clause2] = PASSIVE; _push(clause2, CLAUSE_STACK);
    create_unitclause(lit, clause2, clause_weight[clause2]);
    reduce_clause_weight(clause1, clause_weight[clause2]);
  }
}

int apply_rule1(int var) {
  int *vars_signs, clause, index_var, lit, i, *clauses;
  mark_literals(var);
  for(i=0; i<marked_literals2_stack_fill_pointer; i++)
    in_clause_pos[marked_literals2_stack[i]]=NONE;
  marked_literals2_stack_fill_pointer=0;

  clauses =pos_in[var];
  for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if (clause_state[clause] == ACTIVE) {
      if (clause_length[clause]==2) { //如果有一个clause长度为2
	vars_signs = var_sign[clause];
	for(index_var=*vars_signs; index_var!=NONE; index_var=*(vars_signs+=2)) {
	  if (var_state[index_var]==ACTIVE && index_var != var) {
	    if (*(vars_signs+1) ==TRUE) lit=index_var; else lit=index_var+NB_VAR;
	    if (in_clause_pos[lit] ==NONE) {
	      if (in_clause_neg[lit] != NONE) {
		_push(lit, marked_literals2_stack);
		in_clause_pos[lit]=clause;
	      }
	    }
	    else
	      merge_clause(in_clause_pos[lit], clause);
	    break;
	  }
	}
      }
      else if (clause_length[clause]==1)
	treat_complementary_unitclauses(var, clause);
    }
  }
  for(i=0; i<marked_literals2_stack_fill_pointer; i++) {
    lit=marked_literals2_stack[i];
    treat_binary_clauses(lit, in_clause_pos[lit], in_clause_neg[lit]);
  }

  return TRUE;
}

int apply_rule2(int var) {
  int p_clause, clause, *clauses;

  clauses =neg_in[var];
  MY_UNITCLAUSE_STACK_fill_pointer=0;

 for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if ((clause_state[clause] == ACTIVE) && (clause_length[clause]==1))
	_push(clause, MY_UNITCLAUSE_STACK);
  }
  clauses =pos_in[var];
  for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if ((clause_state[clause] == ACTIVE) && (clause_length[clause]==1))
      treat_complementary_unitclauses(var, clause);
  }
  if (NB_EMPTY>=UB)
    return NONE;
  return TRUE;
}

int rules1_and_2() {
  int var, *clauses, clause, i;
  for(var=0; var<NB_VAR; var++) {
    if (var_state[var]==ACTIVE) {
      if (apply_rule1(var)==NONE)
	       return NONE;
    }
  }
  return TRUE;
}
//------------new var------------
int pos_num,neg_num;
int pos_clause[tab_variable_size],neg_clause[tab_variable_size];
int rec[tab_variable_size][105];
//------------new var
int get_neg_clause_nb(int var) {
  lli_type neg_clause1_nb=0,neg_clause3_nb = 0, neg_clause2_nb = 0;
  int p_clause, clause, *clauses;
  neg_num=0;
  clauses =neg_in[var];

  MY_UNITCLAUSE_STACK_fill_pointer=0;
  for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if ((clause_state[clause] == ACTIVE) && (clause_length[clause]>0)) {
      neg_clause[neg_num++]=clause;
      switch(clause_length[clause]) {
      case 1:
	neg_clause1_nb += clause_weight[clause];
	_push(clause, MY_UNITCLAUSE_STACK);
	break;
      case 2:
	neg_clause2_nb += clause_weight[clause];
	break;
      default:
	neg_clause3_nb += clause_weight[clause];
	break;
      }
    }
  }
  neg_clause[neg_num]=NONE;
  nb_neg_clause_of_length1[var] = neg_clause1_nb;
  nb_neg_clause_of_length2[var] = neg_clause2_nb;
  nb_neg_clause_of_length3[var] = neg_clause3_nb;
  return neg_clause1_nb+neg_clause2_nb + neg_clause3_nb;
}

#define OTHER_LIT_FIXED 1
#define THIS_LIT_FIXED 2

// return remaining clause weight
int treat_complementary_unitclauses(int var, int clause) {
  int clause1;
  while (MY_UNITCLAUSE_STACK_fill_pointer>0) {
    clause1=pop(MY_UNITCLAUSE_STACK);
    if (clause_weight[clause] > clause_weight[clause1]) {
      clause_state[clause1] = PASSIVE; _push(clause1, CLAUSE_STACK);
      nb_neg_clause_of_length1[var] -= clause_weight[clause1];
      NB_EMPTY += clause_weight[clause1];
      reduce_clause_weight(clause, clause_weight[clause1]);
    }
    else if (clause_weight[clause] == clause_weight[clause1]) {
      clause_state[clause1] = PASSIVE; _push(clause1, CLAUSE_STACK);
      clause_state[clause] = PASSIVE; _push(clause, CLAUSE_STACK);
      nb_neg_clause_of_length1[var] -= clause_weight[clause1];
      NB_EMPTY += clause_weight[clause1];
      return 0;
    }
    else {
      clause_state[clause] = PASSIVE; _push(clause, CLAUSE_STACK);
      nb_neg_clause_of_length1[var] -= clause_weight[clause];
      NB_EMPTY += clause_weight[clause];
      reduce_clause_weight(clause1, clause_weight[clause]);
      _push(clause1, MY_UNITCLAUSE_STACK);
      return 0;
    }
  }
  return clause_weight[clause];
}

int get_pos_clause_nb(int var) {
  lli_type pos_clause1_nb=0, pos_clause3_nb = 0, pos_clause2_nb = 0;
  int p_clause, clause, *clauses;
  int flag;
  pos_num=0;
  clauses =pos_in[var];
  for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
    if ((clause_state[clause] == ACTIVE) && (clause_length[clause]>0)) {
      pos_clause[pos_num++]=clause;
      switch(clause_length[clause]) {
      case 1:
	pos_clause1_nb+=treat_complementary_unitclauses(var, clause);
	break;
      case 2:
	pos_clause2_nb += clause_weight[clause];
	break;
      default:
	pos_clause3_nb += clause_weight[clause];
	break;
      }
    }
  }
  pos_clause[pos_num]=NONE;
  nb_pos_clause_of_length1[var] = pos_clause1_nb;
  nb_pos_clause_of_length2[var] = pos_clause2_nb;
  nb_pos_clause_of_length3[var] = pos_clause3_nb;
  return pos_clause1_nb+pos_clause2_nb + pos_clause3_nb;
}

int satisfy_literal(int lit) {
  int var;
  if (positive(lit)) {
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

int assign_value(int var, int current_value, int rest_value) {
  if (var_state[var]==PASSIVE)
    printf("ERROR: Assigning passive variable.\n");
  var_state[var] = PASSIVE;
  _push(var, VARIABLE_STACK);
  var_current_value[var] = current_value;
  var_rest_value[var] = rest_value;
  if (reduce_clauses(var)==NONE)
    return NONE;
  remove_clauses(var);
  return TRUE;
}

int add_to_learned_clause(int clause, int unit_var) {
  int var, *vars_signs;
  int i, j;
  if (clause<INIT_NB_CLAUSE_PREPROC) {
    vars_signs = var_sign[clause];
    for (var = *vars_signs; var != NONE; var = *(vars_signs += 2)) {
      if (var != unit_var) {
	i = 0;
	if (mark[var] > 0) {
	  while (i < POST_UIP_LITS_fill_pointer &&  mark[var] < mark[POST_UIP_LITS[i]])
	    i += 2;
	  if (i == POST_UIP_LITS_fill_pointer || POST_UIP_LITS[i] != var) {
	    for (j = POST_UIP_LITS_fill_pointer - 2; j >= i; j -= 2) {
	      POST_UIP_LITS[j + 2] = POST_UIP_LITS[j];
	      POST_UIP_LITS[j + 3] = POST_UIP_LITS[j + 1];
	    }
	    POST_UIP_LITS[i] = var;
	    POST_UIP_LITS[i + 1] = *(vars_signs + 1);
	    POST_UIP_LITS_fill_pointer += 2;
	  }
	} else {
	  while (i < NEW_CLAUSE_LITS_fill_pointer && NEW_CLAUSE_LITS[i] != var)
	    i += 2;
	  if (i == NEW_CLAUSE_LITS_fill_pointer) {
	    _push(var, NEW_CLAUSE_LITS);
	    _push(*(vars_signs + 1), NEW_CLAUSE_LITS);
	  }
	}
      }
    }
    return TRUE;
  }
  else
    return NONE;
}

void add_clause_to_DB() {
  int var, *vars, *vars_signs;
  int sen;

  if (NEW_CLAUSE_LITS_fill_pointer > MAX_LEN_LEARNED)
    return;
  vars = NEW_CLAUSE_LITS;
  for (var = *vars; var != NONE; var = *(vars += 2)) {
    if (nb_undo_learned[var] >= max_var_learned)
      return;
  }
  BASE_NB_CLAUSE--;
  var_sign[BASE_NB_CLAUSE] = (int *) malloc ((NEW_CLAUSE_LITS_fill_pointer + 1) * sizeof(int));
  vars_signs = var_sign[BASE_NB_CLAUSE];
  vars = NEW_CLAUSE_LITS;
  for (var = *vars; var != NONE; var = *(vars += 2), vars_signs += 2) {
    sen = *(vars + 1);
    *vars_signs = var;
    *(vars_signs + 1) = sen;

   if(sen== POSITIVE) {
		pos_in[var][pos_nb[var]++]=BASE_NB_CLAUSE;
		pos_in[var][pos_nb[var]]=NONE;

   }
   else{
	    neg_in[var][neg_nb[var]++]=BASE_NB_CLAUSE;
	    neg_in[var][neg_nb[var]]=NONE;
   }
   _push(var, POS_NEG_FOR_BACKTRACKING_STACK);
   _push(sen, POS_NEG_FOR_BACKTRACKING_STACK);

    undo_learned[var][nb_undo_learned[var]++] = BASE_NB_CLAUSE;
#ifdef DEBUG
    if (nb_undo_learned[var] > max_var_learned - 5) {
      printf("DEBUG: nb_undo_learned[var].\n");
      exit(0);
    }
#endif
  }
  *vars_signs = NONE;

  clause_length[BASE_NB_CLAUSE] = 0;
  clause_weight[BASE_NB_CLAUSE] = HARD_WEIGHT;
  clause_state[BASE_NB_CLAUSE] = ACTIVE;
}

void hard_learning() {
  int litNum, learning;

  POST_UIP_LITS_fill_pointer = 0;
  NEW_CLAUSE_LITS_fill_pointer = 0;
  learning=add_to_learned_clause(pop(IG_STACK), top(MARK_STACK));
  if (learning !=NONE)
    learning=add_to_learned_clause(pop(IG_STACK), top(MARK_STACK));
  litNum = 0;
  while (POST_UIP_LITS_fill_pointer - litNum > 2 && learning !=NONE) {
    learning=add_to_learned_clause(unit_of_var[POST_UIP_LITS[litNum]],
			  POST_UIP_LITS[litNum]);
    litNum += 2;
  }
  if (learning !=NONE) {
    if (POST_UIP_LITS_fill_pointer > 0) { /// fa falta?
      _push(POST_UIP_LITS[litNum], NEW_CLAUSE_LITS);
      _push(POST_UIP_LITS[litNum + 1], NEW_CLAUSE_LITS);
    }
    _push(NONE, NEW_CLAUSE_LITS);
    add_clause_to_DB();
  }
}

int unitclause_process() {
  int unitclause, var, *vars_signs, unitclause_position,clause, remainingUB;

  IG_STACK_fill_pointer = 0; remainingUB=UB-NB_EMPTY;
  for (unitclause_position = 0;
       unitclause_position < UNITCLAUSE_STACK_fill_pointer;
       unitclause_position++) {
    unitclause = UNITCLAUSE_STACK[unitclause_position];
    if ((clause_state[unitclause] == ACTIVE)  &&
	(clause_length[unitclause]>0) &&
	clause_weight[unitclause] >= remainingUB) {
      vars_signs = var_sign[unitclause];
      for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
	if (var_state[var] == ACTIVE ) {
	  var_current_value[var] = *(vars_signs+1);
	  var_rest_value[var] = NONE;
	  var_state[var] = PASSIVE;
	  _push(var, VARIABLE_STACK);
	  _push(unitclause, IG_STACK);
	  _push(var, MARK_STACK);
	  mark[var] = MARK_STACK_fill_pointer;
	  unit_of_var[var] = unitclause;
	  if ((clause=reduce_clauses(var)) !=NONE) {
	    remove_clauses(var);
	    break;
	  } else {
	    if (partial == 1 && clause_weight[top(IG_STACK)] >= UB) {
	      hard_learning();
	    }
	    while (MARK_STACK_fill_pointer > 0)
	      mark[pop(MARK_STACK)] = NONE;
	    return NONE;
	  }
	}
      }
    }
  }
  while (MARK_STACK_fill_pointer > 0)
    mark[pop(MARK_STACK)] = NONE;
  return TRUE;
}

void search_unit_from_binary() {
  int p_clause, sign, clause, *clauses;
  int var, *vars_signs;
  int lit;
  int search_var;
  int c1, c2;

  for (search_var = 0; search_var < NB_VAR; search_var++) {
    if (var_state[search_var] == ACTIVE) {
      clauses =neg_in[var];
	for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
	if (clause_state[clause] == ACTIVE && clause_length[clause] == 2) {
	  vars_signs = var_sign[clause];
	  for(var = *vars_signs; var != NONE; var = *(vars_signs += 2)) {
	    if (var_state[var] == ACTIVE && var != search_var) {
	      lit = get_lit(var, *(vars_signs + 1));
	      mark[lit] = clause;
	      _push(lit, MARK_STACK);
	      break;
	    }
	  }
	}
      }
    clauses =pos_in[var];
	for(clause=*clauses; clause!=NONE; clause=*(++clauses)) {
	if (clause_state[clause] == ACTIVE && clause_length[clause] == 2) {
	  vars_signs = var_sign[clause];
	  for(var = *vars_signs; var != NONE; var = *(vars_signs += 2)) {
	    if (var_state[var] == ACTIVE && var != search_var) {
	      lit = get_lit(var, *(vars_signs + 1));
	      if (mark[lit] != NONE) {
		if (lit < NB_VAR)
		  sign =POSITIVE;
		else
		  sign =NEGATIVE;
		if (clause_weight[mark[lit]] > clause_weight[clause]) {
		  c1 = clause;
		  c2 = mark[lit];
		} else {
		  c1 = mark[lit];
		  c2 = clause;
		  mark[lit] = NONE;
		}
		_push(c1, CLAUSE_STACK);
		clause_state[c1]=PASSIVE;
		if (clause_weight[c1] == clause_weight[c2]) {
		  _push(c2, CLAUSE_STACK);
		  clause_state[c2]=PASSIVE;
		} else {
		  if (clause_weight[c2] < UB) {
		    _push(c2, SAVED_WEIGHTS_CLAUSE);
#ifdef DEBUG
		    if (SAVED_WEIGHTS_CLAUSE_fill_pointer > tab_clause_size - 5) {
		      printf("DEBUG: SAVED_WEIGHTS_CLAUSE.\n");
		      exit(0);
		    }
#endif
		    _push(clause_weight[c2], SAVED_WEIGHTS_WEIGHT);
		    clause_weight[c2] -= clause_weight[c1];
		  }
		}
		//~ create_unitclause(lit, c1, p_clause_list, clause_weight[c1]);
		create_unitclause(lit, c1, clause_weight[c1]);
		break;
	      }
	    }
	  }
	}
      }
      while (MARK_STACK_fill_pointer > 0)
	mark[pop(MARK_STACK)] = NONE;
    }
  }
}
//----------------NEW----------------
//--------------rule 3-----------------
int temp_clause[tab_variable_size*2][2];
int temp_num,recur_num[tab_variable_size];
int recur[tab_variable_size][50];
bool valid_in_rule6[tab_variable_size];
//bool valid_in_clause[tab_clause_size];
void outputLit(int c){
  int *vars_signs=var_sign[c];
  for (int var=*vars_signs;var!=NONE;var=*(vars_signs+=2)){
      if (var_state[var]!=ACTIVE) continue;
      if (*(vars_signs+1)==POSITIVE) printf("X%d ",var);
                               else  printf("~X%d ",var);
  }
  puts("");
  //puts("\n--------------------------");
}

void create_new_clause(){
  if (temp_num==0){
      NB_EMPTY++;
      return;
  }
  int *new_var_signs=NEW_CLAUSES[NEW_CLAUSES_fill_pointer++]; //新分配一个clause
  int nb=0;
  var_sign[NB_CLAUSE]=new_var_signs; //注意
  for (int index=0;index<temp_num;index++){
      int lit=temp_clause[index][0],c=temp_clause[index][1];
      nb++;
      if (lit<NB_VAR){  //为正
        *(new_var_signs++)=lit;
        *(new_var_signs++)=POSITIVE;
        add_newclause_in(lit,POSITIVE); //-----------
        //replace_clause(NB_CLAUSE,c,pos_in[lit]);
      }else{
        lit-=NB_VAR;
        *(new_var_signs++)=lit;
        *(new_var_signs++)=NEGATIVE;
        add_newclause_in(lit,NEGATIVE); //-----------
       // replace_clause(NB_CLAUSE,c,neg_in[lit]);
      }
  }
  *(new_var_signs)=NONE;
  clause_state[NB_CLAUSE]=ACTIVE;
  clause_length[NB_CLAUSE]=nb;
  clause_weight[NB_CLAUSE]=1;
  if (nb==1) _push(NB_CLAUSE, UNITCLAUSE_STACK);
  NB_CLAUSE++;
}
int rule3num=0;
bool inClause[tab_variable_size*2];
void recovery_inClause(int num){
  for (int index=0;index<num;index++){
    int var=temp_clause[index][0];
    inClause[var]=false;
  }
}
bool rule3(int var,int c1,int c2,int tp){
  if (!DEBUG_OPEN_RULE3) return false;
  rule3num++;
  //往下走都是return true
  //由于var的为正仅包含一个clause,为负仅包含一个clause,所以往下走都是return true
  int *vars_signs;
  _push(var, VARIABLE_STACK);
  var_state[var] = PASSIVE;
  needRecur[var]=tp; //标记,需要递推
  var_current_value[var] = NEGATIVE; // 随意赋值
  var_rest_value[var] = NONE;
  //-----------------构造递推关系
  if (DEBUG_RECUR){
      recur_num[var]=0;
      if (tp==1) vars_signs=var_sign[c2];
            else vars_signs=var_sign[c1];
      for (int lit=*vars_signs;lit!=NONE;lit=*(vars_signs+=2)){
        if (var_state[lit]!=ACTIVE) continue;
        if (*(vars_signs+1)==POSITIVE) recur[var][recur_num[var]++]=lit;        //为正
                                  else recur[var][recur_num[var]++]=lit+NB_VAR;  //为负
      }
  }
  //-----------------构造递推关系
  _push(c1, CLAUSE_STACK); clause_state[c1]=PASSIVE;  //删去c1
  _push(c2, CLAUSE_STACK); clause_state[c2]=PASSIVE;  //删去c2
  temp_num=0;
  vars_signs=var_sign[c1];
  for (int lit=*vars_signs;lit!=NONE;lit=*(vars_signs+=2)){
      if (var_state[lit]!=ACTIVE) continue;
      valid_in_rule6[lit]=true; // for-rule-6
      if (*(vars_signs+1)==POSITIVE){
        temp_clause[temp_num][0]=lit;
        temp_clause[temp_num][1]=c1; //0~NB_VAR-1 为正
        inClause[lit]=true;
        temp_num++;
      }else{
        temp_clause[temp_num][0]=lit+NB_VAR; //为~lit
        temp_clause[temp_num][1]=c1;
        inClause[lit+NB_VAR]=true;
        temp_num++;
      }
  }
  vars_signs=var_sign[c2];
  for (int lit=*vars_signs;lit!=NONE;lit=*(vars_signs+=2)){
      if (var_state[lit]!=ACTIVE) continue;
      valid_in_rule6[lit]=true; // for-rule-6
      if (*(vars_signs+1)==POSITIVE){
        if (inClause[lit]) continue;
        temp_clause[temp_num][0]=lit;
        temp_clause[temp_num][1]=c2; //0~NB_VAR-1 为正
        temp_num++;
        if (inClause[lit+NB_VAR]){
          recovery_inClause(temp_num);
          return true;
        }
      }else{
        if (inClause[lit+NB_VAR]) continue;
        temp_clause[temp_num][0]=lit+NB_VAR; //为~lit
        temp_clause[temp_num][1]=c2;
        temp_num++;
        if (inClause[lit]){
          recovery_inClause(temp_num);
          return true;
        }
      }
  }
  recovery_inClause(temp_num);
  create_new_clause();
  return true;
}
//--------------rule 3-----------------
//-------------------------------rule 6---------------------------------
//----valid的变量才进入操作----
int rule6_1num=0,rule6_2num=0;
int had_var[tab_variable_size][2]; //0负，1正
int rule6_vector[tab_variable_size];
bool run_rule_6_1(int var0,int D,int *b,int sign0){
  bool flagRule6=false,flagRule6_1;
  int *vars_signs0=var_sign[D],Dnum=0;
  for (int var1=*(vars_signs0);var1!=NONE;var1=*(vars_signs0+=2)){
      if (var_state[var1]!=ACTIVE) continue;
      if (var1==var0) continue;
      if (*(vars_signs0+1)==POSITIVE) rule6_vector[Dnum]=var1;
                                 else rule6_vector[Dnum]=var1+NB_VAR;
      had_var[var1][*(vars_signs0+1)]=true;
      Dnum++;
  }
  if (!Dnum) return false;
  int *clauses=b; //i个clause一个个看
  for (int clause=*clauses;clause!=NONE;clause=*(++clauses)){  //扫描i个clause
      vars_signs0=var_sign[clause];
      flagRule6_1=false;
      temp_num=0;
      for (int var1=*vars_signs0;var1!=NONE;var1=*(vars_signs0+=2)){
        if (var_state[var1]!=ACTIVE) continue;
        int sign=*(vars_signs0+1);
        if (had_var[var1][sign]){
            flagRule6_1=true; //可以做rule6.1
            continue;
        }
        if (sign==POSITIVE) temp_clause[temp_num][0]=var1;
                      else  temp_clause[temp_num][0]=var1+NB_VAR;
        temp_clause[temp_num][1]=clause; //0~NB_VAR-1 为正
        temp_num++;
      }
      if (!flagRule6_1) continue;  //能否执行rule6.1
      //-----------run_rule_6_1-------------
      _push(clause, CLAUSE_STACK); clause_state[clause]=PASSIVE;
      create_new_clause();
      rule6_1num++;
      flagRule6=true;
  }
  for (int index=0;index<Dnum;index++){
      int var=rule6_vector[index];
      if (var<NB_VAR) had_var[var][POSITIVE]=false;
                 else had_var[var-NB_VAR][NEGATIVE]=false;
  }
  if (flagRule6==true){
     // outputClause(var0);
  }
  return flagRule6;
}
int store_rule_6_2[MAX_LIT_NUM][3];
bool run_rule_6_2(int var0,int D,int *b,int sign0){
  int D1=-1,num,iNum,Dnum;
  bool flagRule6=false;
  int *vars_signs0=var_sign[D];
  Dnum=0;
  for (int var1=*(vars_signs0);var1!=NONE;var1=*(vars_signs0+=2)){
      if (var_state[var1]!=ACTIVE || var1==var0) continue;
      if (*(vars_signs0+1)==POSITIVE) rule6_vector[Dnum]=var1;
                                 else rule6_vector[Dnum]=var1+NB_VAR;
      Dnum++;
      had_var[var1][*(vars_signs0+1)]=true;
  }
  if (!Dnum) return false;
  int *clauses=b; //i个clause一个个看
  num=iNum=0; //可以做rule6_2规则的个数,先清零
  for (int clause=*clauses;clause!=NONE;clause=*(++clauses)){  //扫描i个clause
      int var1;
      iNum++;
      vars_signs0=var_sign[clause];
      for (var1=*vars_signs0;var1!=NONE;var1=*(vars_signs0+=2)){
          if (var_state[var1]!=ACTIVE) continue;
          int sign=*(vars_signs0+1);
          if (had_var[var1][1-sign]){ //进入rule6.2
            num++;
            store_rule_6_2[num][0]=clause;
            store_rule_6_2[num][1]=var1;
            store_rule_6_2[num][2]=sign;
            break;
          }
      }
      if (var1==NONE){
          D1=clause; //小心处理
      }
  }
  for (int index=0;index<Dnum;index++){
      int var=rule6_vector[index];
      if (var<NB_VAR) had_var[var][POSITIVE]=false;
                 else had_var[var-NB_VAR][NEGATIVE]=false;
  }
  if (num==iNum-1){
    for (int index=1;index<=num;index++){ //把这i-1个clause删去...留下最后一个来做rule3
      int clause=store_rule_6_2[index][0];
      _push(clause,CLAUSE_STACK), clause_state[clause]=PASSIVE;
    }
    if (sign0==POSITIVE) rule3(var0,D,D1,2);
                    else rule3(var0,D1,D,1);
    rule6_2num++;
    return true;
  }

  for (int index=1;index<=num;index++){  //那就拿出来一个个处理
    int clause=store_rule_6_2[index][0],var1=store_rule_6_2[index][1],sign=store_rule_6_2[index][2];
      if (clause_length[clause]>2){
      create_binaryclause(var0,1-sign0,var1,sign,1); //只保留xy
      if (sign0==POSITIVE) nb_neg_clause_of_length2[var0]++;
                      else nb_pos_clause_of_length2[var0]++;
      if (sign==POSITIVE) nb_pos_clause_of_length2[var1]++;
                      else nb_neg_clause_of_length2[var1]++;
      _push(clause,CLAUSE_STACK), clause_state[clause]=PASSIVE; //删除原clause
      flagRule6=true;
      rule6_2num++;
    }
  }
  return flagRule6;
}
bool rule6(int var0){
  int flag=true;
  if (!DEBUG_OPEN_RULE6) return false;
  if (DEBUG_OPEN_RULE3 && !valid_in_rule6[var0]) return false;
  if (pos_num==1){
    if (run_rule_6_2(var0,pos_clause[0],neg_clause,POSITIVE)) {
        return true;  // x (1,i)
    }
    flag=false;
  }
  if (neg_num==1){
    if (run_rule_6_2(var0,neg_clause[0],pos_clause,NEGATIVE)) {
        return true;  // x (i,1)
    }
    flag=false;
  }
  if (DEBUG_OPEN_RULE6_1){
    if (pos_num==1){
         if (run_rule_6_1(var0,pos_clause[0],neg_clause,POSITIVE)) return true;  // x (1,i)
         flag=false;
    }
    if (neg_num==1){
         if (run_rule_6_1(var0,neg_clause[0],pos_clause,NEGATIVE)) return true;  // x (i,1)
         flag=false;
    }
  }
  valid_in_rule6[var0]=flag;
  return false;
}
//-------------------------------rule 6---------------------------------

//----------------NEW----------------
int choose_and_instantiate_variable() {
  int var, chosen_var=NONE,cont=0;
  float poid, max_poid = -1.0;
  NB_BRANCHE++;

   rules1_and_2();
   if (NB_EMPTY>=UB) return NONE;


  if (lookahead()==NONE) return NONE;

  if (NB_BRANCHE==1) INIT_NB_CLAUSE_PREPROC=NB_CLAUSE;

  if (unitclause_process() == NONE) return NONE;

  for (var = 0; var < NB_VAR; var++) {
    if (var_state[var] == ACTIVE) {
      reduce_if_negative[var]=0;
      reduce_if_positive[var]=0;
      if (get_neg_clause_nb(var) == 0) {
	NB_MONO++;
	var_current_value[var] = TRUE;
	var_rest_value[var] = NONE;
	var_state[var] = PASSIVE;
	_push(var, VARIABLE_STACK);
	remove_clauses(var);
      } else if (get_pos_clause_nb(var) == 0) {
	NB_MONO++;
	var_current_value[var] = FALSE;
	var_rest_value[var] = NONE;
	var_state[var] = PASSIVE;
	_push(var, VARIABLE_STACK);
	remove_clauses(var);
      } else if (nb_neg_clause_of_length1[var]+NB_EMPTY>=UB) {
	if (assign_value(var, FALSE, NONE)==NONE)
	  return NONE;
      } else if (nb_pos_clause_of_length1[var]+NB_EMPTY>=UB) {
	if (assign_value(var, TRUE, NONE)==NONE)
	  return NONE;
      } else if (nb_neg_clause_of_length1[var]>=
		 nb_pos_clause_of_length1[var]+
		 nb_pos_clause_of_length2[var]+
		 nb_pos_clause_of_length3[var]) {
	if (assign_value(var, FALSE, NONE)==NONE)
	  return NONE;
      } else if (nb_pos_clause_of_length1[var]>=
		 nb_neg_clause_of_length1[var]+
		 nb_neg_clause_of_length2[var]+
		 nb_neg_clause_of_length3[var]) {
	if (assign_value(var, TRUE, NONE)==NONE)
	  return NONE;
      }else
  if (pos_num==1 && neg_num==1){
         rule3(var,pos_clause[0],neg_clause[0],1);
  }else
  if (rule6(var)){

  }else
	if (nb_neg_clause_of_length1[var]>nb_pos_clause_of_length1[var])
	  cont+=nb_pos_clause_of_length1[var];
   else
	      cont+=nb_neg_clause_of_length1[var];
    }
  }

  if (cont + NB_EMPTY>=UB)
    return NONE;

  for (var = 0; var < NB_VAR; var++) {
    if (var_state[var] == ACTIVE) {
      reduce_if_positive[var] = nb_neg_clause_of_length1[var] * 2
	+ nb_neg_clause_of_length2[var] * 4 + nb_neg_clause_of_length3[var];
      reduce_if_negative[var] = nb_pos_clause_of_length1[var] * 2
	+ nb_pos_clause_of_length2[var] * 4 + nb_pos_clause_of_length3[var];
      poid = reduce_if_positive[var] * reduce_if_negative[var] * 2
	+ reduce_if_positive[var] + reduce_if_negative[var];
      if (poid > max_poid) {
	chosen_var = var;
	max_poid = poid;
      }
    }
  }

  if (chosen_var == NONE) return FALSE;

  saved_clause_stack[chosen_var] = CLAUSE_STACK_fill_pointer;
  saved_reducedclause_stack[chosen_var] = REDUCEDCLAUSE_STACK_fill_pointer;
  saved_unitclause_stack[chosen_var] = UNITCLAUSE_STACK_fill_pointer;
  saved_nb_empty[chosen_var]=NB_EMPTY;
  saved_nb_clause[chosen_var]=NB_CLAUSE;
  saved_saved_clauses[chosen_var]=SAVED_CLAUSES_fill_pointer;
  saved_new_clauses[chosen_var]=NEW_CLAUSES_fill_pointer;
  saved_weights_nb[chosen_var] = SAVED_WEIGHTS_CLAUSE_fill_pointer;

  saved_saved_pos_neg[chosen_var]= POS_NEG_FOR_BACKTRACKING_STACK_fill_pointer;

  if (reduce_if_positive[chosen_var]<reduce_if_negative[chosen_var])
    return assign_value(chosen_var, TRUE, FALSE);
  else
    return assign_value(chosen_var, FALSE, TRUE);
}
int get_current_value(int var){
  if (var_current_value[var]!=DONE) return var_current_value[var];
  for (int index=0;index<recur_num[var];index++){
      int lit=recur[var][index],value;
      if (lit<NB_VAR) value=get_current_value(lit);
                 else value=get_current_value(lit-NB_VAR);
      if (needRecur[var]==1){
        if (lit<NB_VAR  && value==POSITIVE) return var_current_value[var]=POSITIVE;
        if (lit>=NB_VAR && value==NEGATIVE) return var_current_value[var]=POSITIVE;
      }else{
        if (lit<NB_VAR  && value==POSITIVE) return var_current_value[var]=NEGATIVE;
        if (lit>=NB_VAR && value==NEGATIVE) return var_current_value[var]=NEGATIVE;
      }
  }
  if (needRecur[var]==1) return var_current_value[var]=NEGATIVE;
                   else  return var_current_value[var]=POSITIVE;
}
void update_current_value(){
  for (int var=0;var<NB_VAR;var++)
     if (needRecur[var]>0) var_current_value[var]=DONE;
  for (int var=0;var<NB_VAR;var++)
      get_current_value(var);
}
void dpl() {
  lli_type nb;
  int i;
  memset(valid_in_rule6,true,sizeof(valid_in_rule6));
  memset(had_var,false,sizeof(had_var));
  memset(needRecur,0,sizeof(needRecur));
  memset(inClause,false,sizeof(inClause));
  do {
    if (VARIABLE_STACK_fill_pointer==NB_VAR) {
      UB = NB_EMPTY;
      if (DEBUG_RECUR) update_current_value();
      nb = verify_solution();
      if (nb != NB_EMPTY)
	printf("ERROR: Solution verification fails, real_empty = %lli, NB_EMPTY = %lli.\n",
	       nb, NB_EMPTY);
      printf("o %lli\n", UB);
      for (i = 0; i < NB_VAR; i++)
	var_best_value[i] = var_current_value[i];
      while (backtracking()==NONE);
      if (VARIABLE_STACK_fill_pointer==0)
	break;
    }
    //if (UB-NB_EMPTY==1)
    if (unitclause_process() ==NONE)
      while (backtracking()==NONE);
    if (choose_and_instantiate_variable()==NONE)
      while (backtracking()==NONE);
  } while (VARIABLE_STACK_fill_pointer > 0);
}


void init() {
  int var, clause;

  NB_EMPTY=0; REAL_NB_CLAUSE=NB_CLAUSE;
//  UNITCLAUSE_STACK_fill_pointer=0;
  VARIABLE_STACK_fill_pointer=0;
  CLAUSE_STACK_fill_pointer = 0;
  REDUCEDCLAUSE_STACK_fill_pointer = 0;
  for (var=0; var<NB_VAR; var++) {
    in_clause_neg[var]=NONE; in_clause_neg[var+NB_VAR]=NONE;
    in_clause_pos[var]=NONE; in_clause_pos[var+NB_VAR]=NONE;
    reason[var]=NO_REASON;
    fixing_clause[var]=NONE;
    fixing_clause[var+NB_VAR]=NONE;
    lit_involved_in_clause[var]=NONE;
    lit_involved_in_clause[var+NB_VAR]=NONE;
    saved_weights_nb[var] = 0;
    saved_lit_in_stack[var] = 0;
    mark[var] = NONE;
    mark[var + NB_VAR] = NONE;
    nb_undo_learned[var] = 0;

    saved_pos_nb[var]= pos_nb[var];
    saved_neg_nb[var]= neg_nb[var];
  }
  for (clause = 0; clause < tab_clause_size; clause++) {
    clause_involved[clause]=NONE;
    ini_clause_weight[clause] = clause_weight[clause];
    clause_entered[clause]=FALSE;
    in_conflict[clause]=FALSE;
    clause_involved_in_conflict[clause]=FALSE;
    binclause_reducing_reason[clause]=NONE;
    //  clause_involved_fl[clause]=FALSE;
  }
  /*
  for (clause = 0; clause<tab_clause_size; clause++)
    binclause_reducing_reason[clause]=NONE;
  */
  //~ zz_print_structure();

}

void ubcsat(char file[]) {
  int i;
  char str[WORD_LENGTH];
  char fout[WORD_LENGTH];
  char strLS[tab_variable_size + WORD_LENGTH];
  double optimumLS;
  char valuesLS[tab_variable_size + WORD_LENGTH];
  FILE *ls;

  ls = fopen("ubcsat", "r");
  if (ls == (FILE*) NULL) {
    printf("WARNING: Ubcsat not found.\n");
    return;
  }
  sprintf(fout, "/tmp/ubcsat-%i.out", getpid());
  if (instance_type == 0) {
    sprintf(str, "./ubcsat -alg irots -seed 0 -runs 10 -cutoff %i -solve -r bestsol -inst %s | grep \"Run ID\" -A1 | tail -n1 > %s", NB_VAR * 100, file, fout);
  } else {
    sprintf(str, "./ubcsat -alg irots -w -seed 0 -runs 10 -cutoff %i -solve -r bestsol -inst %s | grep \"Run ID\" -A1 | tail -n1 > %s", NB_VAR * 100, file, fout);
  }
  system(str);
  ls = fopen(fout, "r");
  if (ls == (FILE*) NULL) {
    printf("WARNING: Ubcsat output file not found.\n");
    return;
  }
  fgets(strLS, tab_variable_size + WORD_LENGTH, ls);
  fclose(ls);
  remove(fout);
  sscanf(strLS, "%i %i %lf %s", &i, &i, &optimumLS, valuesLS);
  if (optimumLS==0) return;
  // printf("%lf\n%lli\n%s\n", optimumLS, (long long int) optimumLS, valuesLS);
  UB = min(UB, (long long int) optimumLS);
  i = 0;
  while (valuesLS[i] != '\0') {
    if (valuesLS[i] == '1')
      var_best_value[i] = TRUE;
    else
      var_best_value[i] = FALSE;
    i++;
  }
  if (i != NB_VAR) {
    printf("WARNING: Ubcsat problem.\n");
  }
}
char saved_input_file[WORD_LENGTH];
int main(int argc, char *argv[]) {


  struct tms *a_tms;
  FILE *fp_time;
  clock_t begintime, endtime;

  int i;
  if (argc <= 1) {
    printf("Using format: %s input_instance [-l]\n\t-l: without local search.", argv[0]);
    return FALSE;
  }
  for (i=0; i<WORD_LENGTH; i++)
    saved_input_file[i]=argv[1][i];
  begintime = clock();
  //~ a_tms = ( struct tms *) malloc( sizeof (struct tms));
  //~ mess=times(a_tms); begintime = a_tms->tms_utime;

  printf("c ---------------------------------\n");
  printf("c - Weighted Partial maxsatz2013f -\n");
  printf("c ---------------------------------\n");
  printf("c solving instance %s...\n", argv[1]);
#ifdef DEBUG
  printf("c DEBUG mode ON\n");
#endif

  switch (build_simple_sat_instance(argv[1])) {
  case FALSE:
    printf("ERROR: Input file error\n");
    return FALSE;
  case TRUE:
    UB = HARD_WEIGHT;
    if (argc < 3 || strcmp(argv[2], "-l") != 0)
      ubcsat(argv[1]);
    else
      printf("c Without local search.\n");
    printf("o %lli\n", UB);
    if (UB != 0) {
      init();
      dpl();
    }
    break;
  case NONE:
    printf("An empty resolvant is found!\n"); break;
  }
  //~ mess=times(a_tms); endtime = a_tms->tms_utime;
  endtime = clock();

  if (UB >= HARD_WEIGHT) {
    printf("s UNSATISFIABLE\n");
  } else {
    printf("s OPTIMUM FOUND\n");
    printf("v");
    for (i = 0; i < NB_VAR; i++) {
      if (var_best_value[i] == FALSE)
	printf(" -%i", i + 1);
      else
	printf(" %i", i + 1);
    }
    printf(" 0\n");
  }
  printf("c Learned clauses = %i\n", INIT_BASE_NB_CLAUSE - BASE_NB_CLAUSE);
  printf("c NB_MONO= %lli, NB_BRANCHE= %lli, NB_BACK= %lli \n",
	 NB_MONO, NB_BRANCHE, NB_BACK);
  printf ("c Program terminated in %5.3f seconds.\n",
	  (double)(endtime-begintime)/CLOCKS_PER_SEC);
  return TRUE;
}
