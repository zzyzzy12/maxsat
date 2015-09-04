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
void dfs(int x,int m,int &num,int *ans,set<int> *C){
	set<int>::iterator it;
	if (!x){
		int t=0;
		for (int i=1;i<=m;i++)
			for (it=C[i].begin();it!=C[i].end();it++)
				if (ans[*it]){
					t++;
					break;
				}
		num=max(num,t);
		return;
	}
	if (ans[x]==-1){
		ans[x]=0;
		dfs(x-1,m,num,ans,C);
		ans[x]=1;
		dfs(x-1,m,num,ans,C);
	}else
		dfs(x-1,m,num,ans,C);
}
int Lemma6(int n,int m,int *ans,set<int> *C){
	int num=0;
	dfs(n,m,num,ans,C);
	return num;
}