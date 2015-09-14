using namespace std; 
struct node{
	set<int> F;
	int fx;
};
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
void copy(node *H,set<int> *C,node *tH,set<int> *tC,int n,int m,int &tn,int &tm){
	tn=n,tm=m;
	for (int i=1;i<=n;i++) tH[i]=H[i];
	for (int i=1;i<=m;i++) tC[i]=C[i];
}
void back(node *H,set<int> *C,node *tH,set<int> *tC,int &n,int &m,int tn,int tm){
	n=tn,m=tm;
	for (int i=1;i<=n;i++) H[i]=tH[i];
	for (int i=1;i<=m;i++) C[i]=tC[i];
}
bool reNew(int &m,int *X,node *H,set<int> *C){
	set<int>::iterator it;
	for (int i=1;i<=m;i++){
		if (C[i].size()==0){
			C[i]=C[m--];
			return true;
		}
		for (it=C[i].begin();it!=C[i].end();it++){
			if (H[ABS(*it)].fx!=0) continue; //要值确定了才
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