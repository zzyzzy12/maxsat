#include<iostream>
#include<cstdio>
#include<cstring>
#include<algorithm>
#include<cmath>
#include<map>
#include<set>
#include<queue>
#include<stack>
using namespace std;
void searchH(int i,node *H,int *now){
	set<int>::iterator it;
    if (H[i].fx<=0) return; //值是确定的
	if (H[i].fx>1){ //其值依赖于H[i].fx与H[i].F的值
		searchH(H[i].fx,H,now);
		if (now[H[i].fx]==0){
			H[i].fx=0,now[i]=0; //根据第八条规则
			return;
		}
	}
	int t=0;  //只看H[i].F的值
	for (it=H[i].F.begin();it!=H[i].F.end();it++){
		int x=*it;
		searchH(ABS(x),H,now);
		if ((x>0 && now[x]==1) || (x<0 && now[-x]==0)){
			t=1;
			break;
		}
	}
	H[i].fx=0,now[i]=t; 
}
void consH(int n,node *H,node *H0,int *now){
	for (int i=1;i<=n;i++) H0[i]=H[i];
	for (int i=1;i<=n;i++) searchH(i,H,now);
}
void reH(int n,node *H,node *H0){
	for (int i=1;i<=n;i++) H[i]=H0[i];
}
void dfs(int x,int n,int m,int* now,int *ans,int &maxNum,node *H,set<int> *C0){ 
	if (!x){
		node H0[1005];
		consH(n,H,H0,now);
		int t=0; 
		set<int>::iterator it;
		for (int i=1;i<=m;i++)
			for (it=C0[i].begin();it!=C0[i].end();it++){ 
				if ((*it>0 && now[*it]==1) || (*it<0 && now[-*it]==0)){
					t++;
					break;
				}
			}
		if (t>maxNum){
			maxNum=t; 
			for (int i=1;i<=n;i++) ans[i]=now[i];
		}
		reH(n,H,H0);
		return;
	}
	if (H[x].fx==-1){
		now[x]=0;
		dfs(x-1,n,m,now,ans,maxNum,H,C0);
		now[x]=1;
		dfs(x-1,n,m,now,ans,maxNum,H,C0);
	}else
		dfs(x-1,n,m,now,ans,maxNum,H,C0);
}
void Lemma6(int n,int m,int *X,int *ans,int &maxNum,node *H,set<int> *C0){ 
	int now[1005];
	for (int i=1;i<=n;i++) now[i]=X[i];  
	dfs(n,n,m,now,ans,maxNum,H,C0);
	return;
}