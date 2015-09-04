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
bool find(set<int> C,int x){
	return C.find(x)!=C.end();
}
int ABS(int x){
	if (x<0) return -x;
	return x;
}
bool reNew(int n,int &m,int *X,set<int> *C){
	set<int>::iterator it;
	for (int i=1;i<=m;i++){
		if (C[i].size()==0){
			swap(C[i],C[m--]);
			return true;
		}
		for (it=C[i].begin();it!=C[i].end();it++){
			if (X[ABS(*it)]==-1) continue;
			if (X[ABS(*it)]==1){
				if (*it>0) swap(C[i],C[m--]);
					  else C[i].erase(*it); 
			}else{
				if (*it<0) swap(C[i],C[m--]);
					  else C[i].erase(*it); 
			}
			return true;
		}
	}
	return false;
}
bool R_Rules0(int n,int &m,int *X,set<int> *C){
	set<int>::iterator it;
	while (reNew(n,m,X,C));
	for (int i=1;i<=n;i++){
		if (X[i]!=-1) continue;
		int p[3];
		p[0]=p[1]=p[2]=0;
		for (p[0]=1;p[0]<=m;p[0]++)
			if (find(C[p[0]],i) || find(C[p[0]],-i)) break;
		for (p[1]=p[0]+1;p[1]<=m;p[1]++)
			if (find(C[p[1]],i) || find(C[p[1]],-i)) break;
		for (p[2]=p[1]+1;p[2]<=m;p[2]++)
			if (find(C[p[2]],i) || find(C[p[2]],-i)) break;
		if (p[0]>m){
			X[i]=0;
			return true;
		}
		if (p[1]>m){ //----处理只出现在一个F的
			if (find(C[p[0]],i)) X[i]=1;
						   else  X[i]=0; 
			return true;
		}
		if (p[2]>m){  //----处理只出现在两个F的
			if (find(C[p[0]],i) && find(C[p[1]],i)){
				X[i]=1;
				return true;
			}
			X[i]=1;
			for (it=C[p[1]].begin();it!=C[p[1]].end();it++)
				C[p[0]].insert(*it);
			C[p[0]].erase(-i),C[p[0]].erase(i);
			swap(C[p[1]],C[p[m--]]);
			return true;
		}
		//----处理出现在三个F且都相同的
		if (find(C[p[0]],i) && find(C[p[1]],i) && find(C[p[2]],i)){
			X[i]=1; 
			swap(C[p[0]],C[m--]);
			swap(C[p[1]],C[m--]);
			swap(C[p[2]],C[m--]);
			return true;
		}
	}
	return false;
} 