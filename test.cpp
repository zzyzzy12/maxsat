#include<iostream>
#include<cstdio>
#include<cstring>
#include<algorithm>
#include<cmath>
#include<map>
#include<set>
#include<queue>
#include<stack>
#include"head.h"
#include"initial.h"
#include"lemma6.h"
#include"rule1.h"
#include"rule2.h"
#include"rule3.h"
#include"rule5.h"
#include"rule6.h"
#include"rule7.h"
#include"rule8.h"
#include"rule9.h"
using namespace std;
const int MAXN=1005;
bool legalRule4(set<int> c,int x,int m,set<int> *C){
	set<int>::iterator it;
	for (it=c.begin();it!=c.end();it++){
		if (*it==x || singletons(ABS(*it),m,C)) continue;
		return true;
	}
	return false;
}
void n3MaxSAT(int n,int m,int m0,int *X,int *ans,int &maxNum,set<int> *C,set<int> *C0){
	set<int>::iterator it;
	while (1){
		while (reNew(m,X,C));
		if (rule1(n,m,X,C)) continue; //done
		if (rule2(n,m,X,C)) continue; //done
		if (rule3(n,m,X,C)) continue; //done
		if (rule5(n,m,X,C)) continue; //done
		if (rule6(n,m,X,C)) continue;
		if (rule7(n,m,X,C)) continue;
		if (rule8(n,m,X,C)) continue;
		if (rule9(n,m,C))   continue; //done
		break;
	}
	int i;
	for (i=1;i<=n;i++)
		if (X[i]==-1 && !singletons(i,m,C)) break;
	if (!m || i>n){
		Lemma6(n,m0,X,ans,maxNum,C0); 
		return;
	}
	int D=0,t;
	for (t=1;t<=m;t++)
		if (find(C[t],-i)){
			D=C[t].size()-1;
			break;
		}
	if (D>=2 && legalRule4(C[t],i,m,C)){ // |D|=2
		int tn,tm;
		int tX[MAXN];
		set<int> tC[MAXN];
		copy(X,C,tX,tC,n,m,tn,tm);
		X[i]=1; //-----n3MaxSAT(F[x])
		n3MaxSAT(n,m,m0,X,ans,maxNum,C,C0);
		back(X,C,tX,tC,n,m,tn,tm);
		X[i]=0; //-----n3MaxSAT(F[-x,-y1,-y2....])
		for (it=C[t].begin();it!=C[t].end();it++){
			if (X[ABS(*it)]!=-1) continue;
			if (*it>0) X[*it]=0;
				else   X[-*it]=1;
		} 
		n3MaxSAT(n,m,m0,X,ans,maxNum,C,C0);
		back(X,C,tX,tC,n,m,tn,tm);
		return; 
	}else{
		int tn,tm;
		int tX[MAXN];
		set<int> tC[MAXN];
		copy(X,C,tX,tC,n,m,tn,tm);
		X[i]=1;  //-----n3MaxSAT(F[x])
		n3MaxSAT(n,m,m0,X,ans,maxNum,C,C0);
		back(X,C,tX,tC,n,m,tn,tm);
		X[i]=0;  //-----n3MaxSAT(F[-x])
		n3MaxSAT(n,m,m0,X,ans,maxNum,C,C0);
		back(X,C,tX,tC,n,m,tn,tm);
		return; 
	}    
}
int main(){
    freopen("input.txt","r",stdin);
    freopen("output.txt","w",stdout);
    int n,m,m0;
	set<int> C[MAXN],C0[MAXN];
	int ans[MAXN],X[MAXN],t[MAXN],maxNum=0;
    initial(n,m,ans,C0),m0=m;
    memset(t,0,sizeof(t)); // 都转为x x -x
    for (int x=1;x<=n;x++){
    	int m1=0,m2=0;
    	for (int i=1;i<=m;i++){
    		if (C0[i].find(x)!=C0[i].end()) m1++;
    		if (C0[i].find(-x)!=C0[i].end()) m2++;
    	}
    	if (m2>m1){ // -x比x多，则交换-x,x
    		t[x]=1;
    		for (int i=1;i<=m;i++){
    			if (C0[i].find(x)!=C0[i].end()){
    				C0[i].erase(x),C0[i].insert(-x);
    			}else
    			if (C0[i].find(-x)!=C0[i].end()){
    				C0[i].erase(-x),C0[i].insert(x);
    			}
    		}
    	}
    }
    for (int i=1;i<=m;i++) C[i]=C0[i]; 
    memset(X,-1,sizeof(X));  
    n3MaxSAT(n,m,m0,X,ans,maxNum,C,C0);  
	printf("%d\n",maxNum);
    for (int i=1;i<=n;i++)
    	printf("%d ",ans[i]^t[i]); 
    puts("");
    return 0;
}
