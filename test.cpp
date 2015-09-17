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
const int MAXN=205; 
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
	for (int i=1;i<MAXN;i++) tH[i]=H[i]; 
	for (int i=1;i<MAXN;i++) tC[i]=C[i];
}
void back(node *H,set<int> *C,node *tH,set<int> *tC,int &n,int &m,int tn,int tm){
	n=tn,m=tm;
	for (int i=1;i<MAXN;i++) H[i]=tH[i]; 
	for (int i=1;i<MAXN;i++) C[i]=tC[i];
}
bool reFrash(int &m,int *X,node *H,set<int> *C){
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
void initial(int &n,int &m,set<int> *C){ //读取数据
  char s[20];
  //scanf("%s%s%s%s",s,s,s,s); 
  scanf("%d%d",&n,&m); 
  for (int t=1;t<=m;t++){ 
  	int x;
    C[t].clear();
    while (~scanf("%d",&x) && x){ 
      C[t].insert(x); 
    }
  } 
} 
bool rule1(int n,int &m,int *X,node *H,set<int> *C){
	set<int>::iterator it;
	bool f=false;
	for (int i=1;i<=m;i++)
		for (it=C[i].begin();it!=C[i].end();it++){
			if (!find(C[i],-*it)) continue; // -x x 别和X[i]=0,1弄混
			X[ABS(*it)]=1; 
			H[ABS(*it)].fx=0;
			f=true;
			break;
		} 
	for (int x=1;x<=n;x++){
		if (H[x].fx!=-1) continue;  
		int p1,p2;
		for (p1=1;p1<=m;p1++)
			if (find(C[p1],x) && C[p1].size()==1) break;
		if (p1>m) continue; //找不到包含i的unit clause
		for (p2=1;p2<=m;p2++)
			if (find(C[p2],-x) && C[p2].size()==1) break; 
		C[p1]=C[m--];
		C[p2]=C[m--];
		f=true;
	}
	return f;
}
bool rule2(int n,int &m,int *X,node *H,set<int> *C){  //不用管dgree
	for (int z=1;z<=n;z++){
		if (H[z].fx!=-1) continue;
		int p1,p2,h1,h2; //p1= x个数   p2= -x个数  h1 = x unit  h2 = -x unit
		for (int i=1;i<=m;i++){
			if (find(C[i],z)) {
				p1++;
			    if (C[i].size()==1) h1++;
			}
			if (find(C[i],-z)) {
				p2++;
				if (C[i].size()==1) h2++;
			}
		}
		if (h1>=p2){
			H[z].fx=0; //z可以直接赋值
			X[z]=1;
			return true;
		}
		if (h2>=p1){
			H[z].fx=0; //z可以直接赋值
			X[z]=0;
			return true;
		}
	} 
	return false;
}
bool rule3(int n,int &m,int *X,node *H,set<int> *C){
	set<int>::iterator it;
	for (int x=1;x<=n;x++){ 
		int degree=0;
		for (int i=1;i<=m;i++)
			if (find(C[i],x) || find(C[i],-x)) degree++;
		if (degree!=2) continue;
		int c1,c2;
		for (int i=1;i<=m;i++){
			if (find(C[i],x)) c1=i;
			if (find(C[i],-x)) c2=i;
		} 
		C[c1].insert(C[c2].begin(),C[c2].end()); //合并set
		C[c1].erase(x),C[c1].erase(-x);
		H[x].fx=1,H[x].F=C[c2],H[x].F.erase(-x); // x由c2得来
		C[c2]=C[m--];
		return true;
	}
	return false;
}
bool rule5(int n,int &m,int *X,node *H,set<int> *C){ //在实现的时候只需要让x=1 
	int degree[MAXN];
	for (int x=1;x<=n;x++){
		degree[x]=0;
		for (int i=1;i<=m;i++)
			if (find(C[i],x) || find(C[i],-x)) degree[x]++;
	}
	for (int x=1;x<=n;x++){  
		if (H[x].fx!=-1 || degree[x]!=3) continue;  
		int c1,c2,c3;
		for (c1=1;c1<=m;c1++)
			if (find(C[c1],x) || find(C[c1],-x)) break;
		for (c2=c1+1;c2<=m;c2++)
			if (find(C[c2],x) || find(C[c2],-x)) break;
		for (c3=c2+1;c3<=m;c3++)
			if (find(C[c3],x) || find(C[c3],-x)) break;
		int y=0;
		set<int>::iterator it;
		for (it=C[c1].begin();it!=C[c1].end();it++){
			if (!find(C[c2],*it) && !find(C[c2],-*it)) continue;
			if (!find(C[c3],*it) && !find(C[c3],-*it)) continue;
			y=ABS(*it);
			break;
		}
		if (!y || degree[y]!=3) continue;
		/*
		待完善
		*/
		return true;
	}
	return false;
}
bool rule6(int n,int m,node *H,set<int> *C){ //把(~x,~y,C2)中的x去掉 x=(~y,C2) 
	int degree[MAXN];
	for (int x=1;x<=n;x++){
		degree[x]=0;
		for (int i=1;i<=m;i++)
			if (find(C[i],x) || find(C[i],-x)) degree[x]++;
	}
	for (int x=1;x<=n;x++){
		if (H[x].fx!=-1 || degree[x]!=3) continue;
		/*
		待完善
		*/
		return true;
	}
	return false;
}
bool rule7(int n,int &m,int *X,node *H,set<int> *C){
	int degree[MAXN];
	for (int x=1;x<=n;x++){
		degree[x]=0;
		for (int i=1;i<=m;i++)
			if (find(C[i],x) || find(C[i],-x)) degree[x]++;
	}
	for (int x=1;x<=n;x++){
		if (H[x].fx!=-1 || degree[x]!=3) continue;
		/*
		待完善
		*/
		return true;
	}
	return false;
}
bool rule8(int &n,int &m,int *X,node *H,set<int> *C){ // (~x',D1,D2)
	int degree[MAXN];
	for (int x=1;x<=n;x++){
		degree[x]=0;
		for (int i=1;i<=m;i++)
			if (find(C[i],x) || find(C[i],-x)) degree[x]++;
	}
	for (int x=1;x<=n;x++){
		if (H[x].fx!=-1 || degree[x]!=3) continue;
		/*
		待完善
		*/
		return true;
	}
	return false;
}
bool rule9(int n,int &m,set<int> *C){
	set<int>::iterator it;
	for (int i=1;i<=m;i++){
		if (C[i].size()!=2) continue;
		int x[2],t=0;
		for (it=C[i].begin();it!=C[i].end();it++)
			x[t++]=*it;
		int p0,p1;
		for (p0=0;p0<=m;p0++)
			if (C[p0].size()==1 && find(C[p0],1-x[0])) break;
		if (p0>m) continue;
		for (p1=0;p1<=m;p1++)
			if (C[p1].size()==1 && find(C[p1],1-x[1])) break;
		if (p1>m) continue;
		C[i]=C[m--];
		C[p0]=C[m--];
		C[p1]=C[m--];
		C[++m].clear();
		C[m].insert(1-x[0]),C[m].insert(1-x[1]);
		return true;
	}
	return false;
}
void searchH(int i,node *H,int *now){
	set<int>::iterator it;
    if (H[i].fx<=0) return; //值是确定的
	if (H[i].fx>1){ //其值依赖于H[i].fx与H[i].F的值
		searchH(H[i].fx,H,now);
		if (now[H[i].fx]==0){
			H[i].fx=0,now[i]=0; //根据rule8规则
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

void dfs(int x,int n,int m,int* X,int *ans,int &maxNum,node *H,set<int> *C0){ 
	if (!x){
		node H0[MAXN];
		consH(n,H,H0,X); //展开H
		int t=0; 
		set<int>::iterator it; 
		for (int i=1;i<=m;i++)
			for (it=C0[i].begin();it!=C0[i].end();it++){ 
				if ((*it>0 && X[*it]==1) || (*it<0 && X[-*it]==0)){
					t++;
					break;
				}
			}
		if (t>maxNum){
			maxNum=t; 
			for (int i=1;i<=n;i++) ans[i]=X[i]; 
		}
		reH(n,H,H0); //还原H
		return;
	}
	if (H[x].fx==-1){
		X[x]=0;
		H[x].fx=0;
		dfs(x-1,n,m,X,ans,maxNum,H,C0);
		X[x]=1;
		dfs(x-1,n,m,X,ans,maxNum,H,C0);
		H[x].fx=-1;
	}else
		dfs(x-1,n,m,X,ans,maxNum,H,C0);
}  
void branch(int k,int &n,int &m,int *X,int &maxNum,int *ans,set<int> *C,set<int> *C0,node* H){
	/*
		注意x与-x个个数多少不做限制了
	*/
	if (k>n){
		dfs(n,n,m,X,ans,maxNum,H,C0);  
		return;
	} 
	while (1){
		while (reFrash(m,X,H,C)); //done
		if (rule1(n,m,X,H,C)) continue; //done
		if (rule2(n,m,X,H,C)) continue; //done
		if (rule3(n,m,X,H,C)) continue; //done
	//	if (rule5(n,m,X,H,C)) continue; 
	//	if (rule6(n,m,H,C))   continue; 
	//	if (rule7(n,m,X,H,C)) continue; //判断dgree x,y同时出现在两个clause用O(n)的
	//	if (rule8(n,m,X,H,C)) continue; 
		if (rule9(n,m,C))     continue; 
		break;
	} 
	int num=0;
	set<int> tC[MAXN];
	node tH[MAXN];
	int tn,tm;
	for (int i=1;i<=m;i++)
		if (find(C0[i],k) || find(C0[i],-k)) num++; 
	if (num>3 && H[k].fx==-1){ //degree>3的先分支 
		copy(H,C,tH,tC,n,m,tn,tm); //保护现场
		H[k].fx=0; //值确定
		X[k]=0;
		branch(k+1,n,m,X,maxNum,ans,C,C0,H);
		back(H,C,tH,tC,n,m,tn,tm); //还原现场
		X[k]=1;
		branch(k+1,n,m,X,maxNum,ans,C,C0,H);
		back(H,C,tH,tC,n,m,tn,tm);
	}else{
		copy(H,C,tH,tC,n,m,tn,tm); //保护现场
		branch(k+1,n,m,X,maxNum,ans,C,C0,H); 
		back(H,C,tH,tC,n,m,tn,tm); //还原现场
	}
}
int main(){
    freopen("sgen1-unsat-61-100.cnf","r",stdin);
    freopen("output.txt","w",stdout);
    int n,m,maxNum=0;
	set<int> C[MAXN],C0[MAXN];
	int ans[MAXN],X[MAXN];
    node H[MAXN]; 
    initial(n,m,C0);
    memset(X,-1,sizeof(X));  
	for (int i=0;i<MAXN;i++) H[i].fx=-1;
	for (int i=1;i<=m;i++) C[i]=C0[i]; 
	branch(1,n,m,X,maxNum,ans,C,C0,H); //将实例转为n3-Max-SAT 
	printf("%d\n",maxNum);
	for (int i=1;i<=n;i++) printf("%d ",ans[i]);
	puts(""); 
    return 0;
}
