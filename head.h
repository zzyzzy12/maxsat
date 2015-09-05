using namespace std; 
bool find(set<int> C,int x){
	return C.find(x)!=C.end();
}
int ABS(int x){
	if (x<0) return -x;
	return x;
}
bool singletons(int x,int m,set<int> *C){ //严格来说是-x只出现在一个clause中
	for (int i=1;i<=m;i++){
		if (find(C[i],-x) && C[i].size()==1) return true; 
	}
	return false;
}
void copy(int *X,set<int> *C,int *tX,set<int> *tC,int n,int m,int &tn,int &tm){
	tn=n,tm=m;
	for (int i=1;i<=n;i++) tX[i]=X[i];
	for (int i=1;i<=m;i++) tC[i]=C[i];
}
void back(int *X,set<int> *C,int *tX,set<int> *tC,int &n,int &m,int tn,int tm){
	n=tn,m=tm;
	for (int i=1;i<=n;i++) X[i]=tX[i];
	for (int i=1;i<=m;i++) C[i]=tC[i];
}
bool reNew(int &m,int *X,set<int> *C){
	set<int>::iterator it;
	for (int i=1;i<=m;i++){
		if (C[i].size()==0){
			C[i]=C[m--];
			return true;
		}
		for (it=C[i].begin();it!=C[i].end();it++){
			if (X[ABS(*it)]==-1) continue;
			if (X[ABS(*it)]==1){
				if (*it>0) C[i]=C[m--];
					  else C[i].erase(*it); 
			}else{
				if (*it<0) C[i]=C[m--];
					  else C[i].erase(*it); 
			}
			return true;
		}
	}
	return false;
}