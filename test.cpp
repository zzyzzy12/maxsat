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
set<int>::iterator it;
bool isNum(char c){
	if (c>='0' && c<='9') return true;
	if (c=='-') return true;
	return false;
}
bool find(set<int> C,int x){
	return C.find(x)!=C.end();
}
int ABS(int x){
	if (x<0) return -x;
	return x;
}
void initial(int &n,int &m,int *ans,set<int> *C){ //读取数据
	char s[MAXN];
	scanf("%d%d",&n,&m);
    for (int t=1;t<=m;t++){
    	gets(s);
        int len=strlen(s);
        C[t].clear();
        for (int i=0;i<len;i++){
          	if (!isNum(s[i])) continue;
          	int k=1;
          	if (s[i++]=='-') k=-1;
          	int x=0;
          	while (isNum(s[i])) x=x*10+s[i++]-'0';
          	x*=k;
          	C[t].insert(x);
        }
    }
}
bool reNew(int n,int &m,int &num,int *ans,set<int> *C){
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
bool R_Rules(int n,int &m,int &num,int *ans,set<int> *C){
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
bool singletons(int x,int m,set<int> *C){
	for (int i=1;i<=m;i++)
		if (find(C[i],x) && C[i].size()==1) return true;
	return false;
}
void dfs(int x,int m,int &num,int *ans,set<int> *C){
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
	while (R_Rules(n,m,num,ans,C));
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
