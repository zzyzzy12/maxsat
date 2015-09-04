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
const int MAXN=1005;
bool find(set<int> C,int x){
	return C.find(x)!=C.end();
}
int ABS(int x){
	if (x<0) return -x;
	return x;
}
bool reNew(int n,int &m,int &num,int *ans,set<int> *C){
	set<int>::iterator it;
	for (int i=1;i<=m;i++)
		for (it=C[i].begin();it!=C[i].end();it++){
			if (ans[ABS(*it)]==-1) continue;
			if (ans[ABS(*it)]==1){
				if (*it>0) swap(C[i],C[m--]),num++;
					  else C[i].erase(*it); 
			}else{
				if (*it<0) swap(C[i],C[m--]),num++;
					  else C[i].erase(*it); 
			}
			return true;
		}
	return false;
}
bool R_Rules0(int n,int &m,int &num,int *ans,set<int> *C){
	set<int>::iterator it;
	while (reNew(n,m,num,ans,C));
	for (int x=1;x<=n;x++){
		if (ans[x]!=-1) continue;
		int p[3];
		p[0]=p[1]=p[2]=0;
		for (p[0]=1;p[0]<=m;p[0]++)
			if (find(C[p[0]],x) || find(C[p[0]],-x)) break;
		for (p[1]=p[0]+1;p[1]<=m;p[1]++)
			if (find(C[p[1]],x) || find(C[p[1]],-x)) break;
		for (p[2]=p[1]+1;p[2]<=m;p[2]++)
			if (find(C[p[2]],x) || find(C[p[2]],-x)) break;
		if (p[0]>m){
			ans[x]=1;
			return true;
		}
		if (p[1]>m){ //----处理只出现在一个F的
			if (find(C[p[0]],x)){
				ans[x]=1;
			}else{
				ans[x]=0;
			}
			return true;
		}
		if (p[2]>m){  //----处理只出现在两个F的
			if (find(C[p[0]],x) && find(C[p[1]],x)){
				ans[x]=1;
				return true;
			}
			if (find(C[p[0]],-x) && find(C[p[1]],-x)){
				ans[x]=0;
				return true;			
			}
			ans[x]=1;
			for (it=C[p[1]].begin();it!=C[p[1]].end();it++)
				C[p[0]].insert(*it);
			C[p[0]].erase(-x),C[p[0]].erase(x);
			swap(C[p[1]],C[p[m--]]),num++;
			return true;
		}
		//----处理出现在三个F且都相同的
		if (find(C[p[0]],x) && find(C[p[1]],x) && find(C[p[2]],x)){
			ans[x]=1; 
			return true;
		}
		if (find(C[p[0]],-x) && find(C[p[1]],-x) && find(C[p[2]],-x)){
			ans[x]=0;
			return true;
		}
	}
	return false;
} 