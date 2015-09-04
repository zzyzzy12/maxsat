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
void dfs(int x,int n,int m,int &num,int* now,int *ans,set<int> *C){
	set<int>::iterator it;
	if (!x){
		int t=0;
		for (int i=1;i<=m;i++)
			for (it=C[i].begin();it!=C[i].end();it++)
				if ((*it>0 && now[*it]==1) || (*it<0 && now[-*it]==0)){
					t++;
					break;
				}
		if (t>num){
			num=t;
			for (int i=1;i<=n;i++) ans[i]=now[i];
		}
		return;
	}
	if (now[x]==-1){
		now[x]=0;
		dfs(x-1,n,m,num,now,ans,C);
		now[x]=1;
		dfs(x-1,n,m,num,now,ans,C);
	}else
		dfs(x-1,n,m,num,now,ans,C);
}
int Lemma6(int n,int m,int *ans,set<int> *C){
	int num=0;
	int now[1005];
	for (int i=1;i<=n;i++) now[i]=ans[i];
	dfs(n,n,m,num,now,ans,C);
	return num;
}