/* test if the new clause is redundant or subsompted by another */
#define OLD_CLAUSE_REDUNDANT -77
#define NEW_CLAUSE_REDUNDANT -7

int smaller_than(int lit1, int lit2) {
  return ((lit1<NB_VAR) ? lit1 : lit1-NB_VAR) < 
    ((lit2<NB_VAR) ? lit2 : lit2-NB_VAR);
}

my_type redundant(int *new_clause, int *old_clause) {
  int lit1, lit2, old_clause_diff=0, new_clause_diff=0;
    
  lit1=*old_clause; lit2=*new_clause;
  while ((lit1 != NONE) && (lit2 != NONE)) {
    if (smaller_than(lit1, lit2)) {
      lit1=*(++old_clause); old_clause_diff++;
    }
    else
      if (smaller_than(lit2, lit1)) {
	lit2=*(++new_clause); new_clause_diff++;
      }
      else
	if (complement(lit1, lit2)) {
	  return FALSE; /* old_clause_diff++; new_clause_diff++; j1++; j2++; */
	}
	else {
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

void remove_passive_clauses() { //删去值为负的clause
  int  clause, put_in, first=NONE;
  for (clause=0; clause<NB_CLAUSE; clause++) {
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
	put_in++;
      }
    }
    NB_CLAUSE=put_in;
  }
}
 
void remove_passive_vars_in_clause(int clause) {  //删去clause中值为负的
  int *vars_signs, *vars_signs1, var, var1, first=NONE;
  vars_signs=var_sign[clause];
  for(var=*vars_signs; var!=NONE; var=*(vars_signs+=2)) {
    if (var_state[var]!=ACTIVE) {
      first=var; break;
    }
  }
  if (first!=NONE) {
    for(vars_signs1=vars_signs+2, var1=*vars_signs1; var1!=NONE; 
	var1=*(vars_signs1+=2)) {
      if (var_state[var1]==ACTIVE) {
	*vars_signs=var1; *(vars_signs+1) = *(vars_signs1+1);
	vars_signs+=2;
      }
    }
    *vars_signs=NONE;
  }
}

int clean_structure() {  //整理clause
  int clause, var, *vars_signs;
  remove_passive_clauses();  //删去值为负的clause
  if (NB_CLAUSE==0) return FALSE;
  for (clause=0; clause<NB_CLAUSE; clause++) 
    remove_passive_vars_in_clause(clause); //删去clause中为负的变量
  for (var=0; var<NB_VAR; var++) { 
    neg_nb[var] = 0;
    pos_nb[var] = 0;
  }
  for (clause=0; clause<NB_CLAUSE; clause++) {
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

void lire_clauses(FILE *fp_in) {
  int i, j, jj, ii, length, tautologie, lits[1000], lit, lit1;
  for (i=0; i<NB_CLAUSE; i++) {
    length=0; 
    fscanf(fp_in, "%d", &lits[length]);
    while (lits[length] != 0) {  // --每个读到0结束--
      length++;
      fscanf(fp_in, "%d", &lits[length]);
    } 
    tautologie = FALSE;  // --原始定义，怎么都会满足 --
    /* test if some literals are redundant and sort the clause */
    for (ii=0; ii<length-1; ii++) { // --排序--
      lit = lits[ii];
      for (jj=ii+1; jj<length; jj++) {
	if (abs(lit)>abs(lits[jj])) {
	  lit1=lits[jj]; lits[jj]=lit; lit=lit1;
	}
	else
	  if (lit == lits[jj]) { //
	    lits[jj] = lits[length-1]; 
	    jj--; length--; lits[length] = 0;
	    printf("literal %d is redundant in clause %d \n", lit, i+1);
	  }
	  else
            if (abs(lit) == abs(lits[jj])) {
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
      clause_state[i] = ACTIVE;
    }
    else { i--; NB_CLAUSE--;}
  }
}

void build_structure() {
  int i, j, var, *lits1, length, clause, *vars_signs, lit;
  for (i=0; i<NB_VAR; i++) { 
    neg_nb[i] = 0; pos_nb[i] = 0;
  }
  for (i=0; i<NB_CLAUSE; i++) {
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
  for(clause=0;clause<NB_CLAUSE;clause++) {
    length = clause_length[clause];
    var_sign[clause] = (int *)malloc((2*length+1)*sizeof(int));
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
    neg_in[i] = (int *)malloc((neg_nb[i]+1) * sizeof(int));
    pos_in[i] = (int *)malloc((pos_nb[i]+1) * sizeof(int));
    neg_in[i][neg_nb[i]]=NONE; pos_in[i][pos_nb[i]]=NONE;
    neg_nb[i] = 0; pos_nb[i] = 0;
    var_state[i] = ACTIVE;
  }   
  for (i=0; i<NB_CLAUSE; i++) {
    // if (i==774)
    //  printf("kjhsdf");
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
  int *lits, i, lit, *clauses, res, clause;

  for (i=0; i<NB_CLAUSE; i++) {
    if (clause_state[i]==ACTIVE) {
      if (clause_length[i]==1)
	_push(i, UNITCLAUSE_STACK);
    }
  }
}

my_type build_simple_sat_instance(char *input_file) {
  FILE* fp_in=fopen(input_file, "r"); //--在文件中读--
  char ch, word2[WORD_LENGTH];
  int i, j, length, NB_CLAUSE1, res, ii, jj, tautologie, lit1,
    lits[1000], *lits1, lit, var, *pos_nb, *neg_nb;
  int clause,*vars_signs,cpt;
  if (fp_in == NULL) return FALSE; //--无此文件--

  fscanf(fp_in, "%c", &ch);
  while (ch!='p') {
    while (ch!='\n') fscanf(fp_in, "%c", &ch);  
    fscanf(fp_in, "%c", &ch);
  }
  
  fscanf(fp_in, "%s%d%d", word2, &NB_VAR, &NB_CLAUSE); //--读入litral个数，clause个数--
  INIT_NB_CLAUSE = NB_CLAUSE;   //记录原始clause个数

  lire_clauses(fp_in); //读每个clause
  fclose(fp_in);
  build_structure();
  eliminate_redundance();
  if (clean_structure()==FALSE)
    return FALSE;
  return TRUE;
}

