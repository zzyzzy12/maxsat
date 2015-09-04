#include<iostream>
#include<cstdio>
#include<cstring>
#include<algorithm>
#include<cmath>
#include<map>
#include<set>
#include<queue>
#include<stack>
#include"initial.h"
#include"lemma6.h"
#include"r_rule0.h"
using namespace std;
const int MAXN=1005;
bool singletons(int x,int m,set<int> *C){
	for (int i=1;i<=m;i++)
		if (find(C[i],x) && C[i].size()==1) return true;
	return false;
}
void copy(int *ans,set<int> *C,int *tans,set<int> *tC,int n,int m,int &tn,int &tm){
	tn=n,tm=m;
	for (int i=1;i<=n;i++) tans[i]=ans[i];
	for (int i=1;i<=m;i++) tC[i]=C[i];
}
void back(int *ans,set<int> *C,int *tans,set<int> *tC,int &n,int &m,int tn,int tm){
	n=tn,m=tm;
	for (int i=1;i<=n;i++) ans[i]=tans[i];
	for (int i=1;i<=m;i++) C[i]=tC[i];
}
int n3MaxSAT(int n,int m,int *ans,set<int> *C){
	int num=0,x;
	set<int>::iterator it;
	while (R_Rules0(n,m,num,ans,C));
	for (x=1;x<=n;x++)
		if (ans[x]==-1 && !singletons(x,m,C)) break;
	if (!m || x>n) return num+Lemma6(n,m,ans,C);
	int m1,m2;
	m1=m2=0;
	for (int i=1;i<=m;i++){
		if (find(C[i],x)) m1++;
		if (find(C[i],-x)) m2++;
	}
	if (m1==1){ // -x,-x,x
		int D=0,t;
		for (t=1;t<=m;t++)
			if (find(C[t],x)){
				D=C[t].size()-1;
				break;
			}
		if (D==2){
			int t1,t2,tn,tm;
			int tans[MAXN];
			set<int> tC[MAXN];
			copy(ans,C,tans,tC,n,m,tn,tm);
			ans[x]=0; //-----n3MaxSAT(F[x])
			t1=n3MaxSAT(n,m,ans,C);
			back(ans,C,tans,tC,n,m,tn,tm);
			ans[x]=1; //-----n3MaxSAT(F[-x,-y1,-y2....])
			for (it=C[t].begin();it!=C[t].end();it++){
				if (ans[ABS(*it)]!=-1) continue;
				if (*it>0) ans[ABS(*it)]=0;
					else   ans[ABS(*it)]=1;
			} 
			t2=n3MaxSAT(n,m,ans,C);
			num+=max(t1,t2); 
		}else{
			int t1,t2,tn,tm;
			int tans[MAXN];
			set<int> tC[MAXN];
			copy(ans,C,tans,tC,n,m,tn,tm);
			ans[x]=1;  //-----n3MaxSAT(F[x])
			t1=n3MaxSAT(n,m,ans,C);
			back(ans,C,tans,tC,n,m,tn,tm);
			ans[x]=0;  //-----n3MaxSAT(F[-x])
			t2=n3MaxSAT(n,m,ans,C);
			num+=max(t1,t2); 
		}
	}else{ // x,x,-x
		int D=0,t;
		for (t=1;t<=m;t++)
			if (find(C[t],-x)){
				D=C[t].size()-1;
				break;
			}
		if (D==2){ // |D|=2
			int t1,t2,tn,tm;
			int tans[MAXN];
			set<int> tC[MAXN];
			copy(ans,C,tans,tC,n,m,tn,tm);
			ans[x]=1; //-----n3MaxSAT(F[x])
			t1=n3MaxSAT(n,m,ans,C);
			back(ans,C,tans,tC,n,m,tn,tm);
			ans[x]=0; //-----n3MaxSAT(F[-x,-y1,-y2....])
			for (it=C[t].begin();it!=C[t].end();it++){
				if (ans[ABS(*it)]!=-1) continue;
				if (*it>0) ans[ABS(*it)]=0;
					else   ans[ABS(*it)]=1;
			} 
			t2=n3MaxSAT(n,m,ans,C);
			num+=max(t1,t2); 
		}else{
			int t1,t2,tn,tm;
			int tans[MAXN];
			set<int> tC[MAXN];
			copy(ans,C,tans,tC,n,m,tn,tm);
			ans[x]=1;  //-----n3MaxSAT(F[x])
			t1=n3MaxSAT(n,m,ans,C);
			back(ans,C,tans,tC,n,m,tn,tm);
			ans[x]=0;  //-----n3MaxSAT(F[-x])
			t2=n3MaxSAT(n,m,ans,C);
			num+=max(t1,t2); 
		}  
	}
	return num;
}
int main(){
    freopen("input.txt","r",stdin);
    freopen("output.txt","w",stdout);
    int n,m;
	set<int> C[MAXN];
	int ans[MAXN];
    initial(n,m,ans,C);
    memset(ans,-1,sizeof(ans)); 
    printf("%d\n",n3MaxSAT(n,m,ans,C));  
    return 0;
}
