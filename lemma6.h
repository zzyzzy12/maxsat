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
void dfs(int x,int n,int m,int* now,int *ans,int &maxNum,set<int> *C0){
	set<int>::iterator it;
	if (!x){
		int t=0;
		for (int i=1;i<=m;i++)
			for (it=C0[i].begin();it!=C0[i].end();it++)
				if ((*it>0 && now[*it]==1) || (*it<0 && now[-*it]==0)){
					t++;
					break;
				}
		if (t>maxNum){
			maxNum=t;
			for (int i=1;i<=n;i++) ans[i]=now[i];
		}
		return;
	}
	if (now[x]==-1){
		now[x]=0;
		dfs(x-1,n,m,now,ans,maxNum,C0);
		now[x]=1;
		dfs(x-1,n,m,now,ans,maxNum,C0);
	}else
		dfs(x-1,n,m,now,ans,maxNum,C0);
}
void Lemma6(int n,int m,int *X,int *ans,int &maxNum,set<int> *C0){ 
	int now[1005];
	for (int i=1;i<=n;i++) now[i]=X[i];
	dfs(n,n,m,now,ans,maxNum,C0);
	return;
}