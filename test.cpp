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
void copy(node *H,int *T,set<int> *C,node *tH,int *tT,set<int> *tC,int n,int m,int &tn,int &tm){
	tn=n,tm=m;
	for (int i=1;i<MAXN;i++) tH[i]=H[i];
	for (int i=1;i<MAXN;i++) tT[i]=T[i];
	for (int i=1;i<MAXN;i++) tC[i]=C[i];
}
void back(node *H,int *T,set<int> *C,node *tH,int *tT,set<int> *tC,int &n,int &m,int tn,int tm){
	n=tn,m=tm;
	for (int i=1;i<MAXN;i++) H[i]=tH[i];
	for (int i=1;i<MAXN;i++) T[i]=tT[i];
	for (int i=1;i<MAXN;i++) C[i]=tC[i];
}
bool reFrash(int n,int &m,int *X,node *H,int *T,set<int> *C){
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
	for (int x=1;x<=n;x++){ // 负的比正的多，交换正负
		int num0=0,num1=0;
		for (int i=1;i<=m;i++){
			if (find(C[i],x)) num0++;
			if (find(C[i],-x)) num1++;
		}
		if (num0>=num1) continue;
		T[x]=1-T[x];
		for (int i=1;i<=m;i++){
			if (find(C[i],x)) C[i].erase(x),C[i].insert(-x);
			else
			if (find(C[i],-x)) C[i].erase(-x),C[i].insert(x);
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
		} //done
	for (int i=1;i<=n;i++){
		if (H[i].fx!=-1) continue;
		int p1,p2,num=0;
		for (int j=1;j<=m;j++)
			if (find(C[j],i) || find(C[j],-i)) num++;
		if (num>3) continue;
		for (p1=1;p1<=m;p1++)
			if (find(C[p1],i) && C[p1].size()==1) break;
		if (p1>m) continue;
		for (p2=1;p2<=m;p2++)
			if (find(C[p2],-i) && C[p2].size()==1) break;
		if (p2>m) continue;
		X[i]=1;
		H[i].fx=0;
		f=true;
	}
	return f;
}
bool rule2(int n,int &m,int *X,node *H,set<int> *C){ 
	for (int z=1;z<=n;z++){
		if (H[z].fx!=-1) continue;
		int i,j,t;
		i=j=t=0;
		for (int k=1;k<=m;k++){
			if (find(C[k],z)){
				i++;
				if (C[k].size()==1) t++;
			} 
			if (find(C[k],-z)) j++;
		}
		if (t<j) continue; 
		X[z]=1;
		H[z].fx=0; //z值确定
		return true;
	} 
	return false;
}
bool rule3(int n,int &m,int *X,node *H,set<int> *C){
	set<int>::iterator it;
	for (int i=1;i<=n;i++){
		if (H[i].fx!=-1) continue;
		int p[3];
		p[0]=p[1]=p[2]=0;
		for (p[0]=1;p[0]<=m;p[0]++)
			if (find(C[p[0]],i) || find(C[p[0]],-i)) break;
		for (p[1]=p[0]+1;p[1]<=m;p[1]++)
			if (find(C[p[1]],i) || find(C[p[1]],-i)) break;
		for (p[2]=p[1]+1;p[2]<=m;p[2]++)
			if (find(C[p[2]],i) || find(C[p[2]],-i)) break;
		if (p[0]>m){ //clause中无i,任意赋值
			X[i]=1;
			H[i].fx=0; //值为0/1
			return true;
		}
		if (p[1]>m){ //----处理只出现在一个F的
			if (find(C[p[0]],i)) X[i]=1;
						   else  X[i]=0;  
			H[i].fx=0; //值为0/1 不用看H[i].F
			return true;
		}
		if (p[2]>m){  //----处理只出现在两个F的
			if (find(C[p[0]],i) && find(C[p[1]],i)){
				X[i]=1;
				H[i].fx=0;
				return true;
			} 
			if (find(C[p[1]],i)) swap(p[0],p[1]);

			H[i].fx=1,H[i].F=C[p[1]],H[i].F.erase(-i); //值由H[i].F决定，而不看H[i].fx

			for (it=C[p[1]].begin();it!=C[p[1]].end();it++)
				C[p[0]].insert(*it);
			C[p[0]].erase(-i),C[p[0]].erase(i);
			C[p[1]]=C[p[m--]];
			return true;
		}
		//----处理出现在三个F且都相同的
		if (find(C[p[0]],i) && find(C[p[1]],i) && find(C[p[2]],i)){
			X[i]=1;  
			H[i].fx=0;
			return true;
		}
	}
	return false;
}
bool rule5(int n,int &m,int *X,node *H,set<int> *C){ //在实现的时候只需要让x=1 
	for (int x=1;x<=n;x++){
		if (H[x].fx!=-1) continue; 
		for (int y=1;y<=n;y++){
			if (H[y].fx!=-1) continue;
			int count=0;
			for (int i=1;i<=m;i++){
				if (!find(C[i],x) && !find(C[i],-x)) continue;
				if (!find(C[i],y) && !find(C[i],-y)) break;
			}
			if (count!=3) continue;
			X[x]=1;
			H[x].fx=0;
			return true;
		}
	}
	return false;
}
bool rule6(int n,int m,node *H,set<int> *C){ //把(~x,~y,C2)中的x去掉 x=(~y,C2) 
	for (int x=1;x<=n;x++){
		if (H[x].fx!=-1) continue;
		for (int y=1;y<=n;y++){
			if (H[y].fx!=-1) continue;
			int p1=0,p2=0; 
			for (int i=1;i<=m;i++){
				if (find(C[i],x) && find(C[i],y)) p1=i;
				if (find(C[i],-x) && find(C[i],-y)) p2=i;
			}
			if (!p1 || !p2) continue;
			C[p2].erase(-x);
			return true;
		}
	}
	return false;
}
bool rule7(int n,int &m,int *X,node *H,set<int> *C){
	int p[2][2];
	for (int x=1;x<=n;x++){
		if (H[x].fx!=-1) continue;
		int t1,t2;
		t1=t2=0;
		for (int i=1;i<=m;i++){
			if (find(C[i],x)) p[0][t1++]=i;
			if (find(C[i],-x)) p[1][t2++]=i;
		}
		if (t1!=2 || t2!=1) continue;
		for (int y=1;y<=n;y++){
			if (H[y].fx!=-1) continue;
			if (find(C[p[1][0]],y)) continue; //小改 交换了y -y
			if (find(C[p[0][0]],-y) && find(C[p[0][1]],y)){
				C[p[0][1]].erase(x);
				return true;
			}
			if (find(C[p[0][0]],y) && find(C[p[0][1]],-y)){
				C[p[0][0]].erase(x);
				return true;
			}
		}
	}
	return false;
}
bool rule8(int &n,int &m,int *X,node *H,set<int> *C){ // (~x',D1,D2)
    set<int>::iterator it;
    for (int x=1;x<=n;x++){
    	if (H[x].fx!=-1) continue;
    	for (int y=1;y<=n;y++){
    		if (H[y].fx!=-1) continue;
    		int c[2],cn,d[2];
    		cn=0;
    		for (int i=1;i<=m;i++){
    			if (find(C[i],x) && find(C[i],y)) c[cn++]=i;
    			if (find(C[i],-x)) d[0]=i;
    			if (find(C[i],-y)) d[1]=i; 
    		}
    		if (cn!=2) continue;
    		H[y].F.clear(),H[y].F.insert(-x);
    		H[x].F=C[d[0]],H[x].F.erase(-x);
    		H[++n].fx=-1;
    		H[x].fx=n,H[y].fx=n;
    		C[c[0]].erase(x),C[c[0]].erase(y),C[c[0]].insert(n);
    		C[c[1]].erase(x),C[c[1]].erase(y),C[c[1]].insert(n);
    		for (it=C[d[1]].begin();it!=C[d[1]].end();it++)
    			C[d[0]].insert(*it);
    		C[d[1]]=C[m--];
    		C[d[0]].erase(-x),C[d[0]].erase(-y),C[d[0]].insert(-n);
    		return true;
    	}
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

void dfs(int x,int n,int m,int* X,int *ans,int &maxNum,node *H,int *T,set<int> *C0){ 
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
		dfs(x-1,n,m,X,ans,maxNum,H,T,C0);
		X[x]=1;
		dfs(x-1,n,m,X,ans,maxNum,H,T,C0);
		H[x].fx=-1;
	}else
		dfs(x-1,n,m,X,ans,maxNum,H,T,C0);
}  
void branch(int k,int &n,int &m,int *X,int &maxNum,int *ans,int *T,set<int> *C,set<int> *C0,node* H){
	if (k>n){
		dfs(n,n,m,X,ans,maxNum,H,T,C0);  //注意带入的T
		return;
	} 
	while (1){
		while (reFrash(n,m,X,H,T,C)); //done
		//if (rule1(n,m,X,H,C)) continue; //done
		//if (rule2(n,m,X,H,C)) continue; 
	//	if (rule3(n,m,X,H,C)) continue; 
	//	if (rule5(n,m,X,H,C)) continue; 
	//	if (rule6(n,m,H,C))   continue; 
	//	if (rule7(n,m,X,H,C)) continue; 
	//	if (rule8(n,m,X,H,C)) continue; 
	//	if (rule9(n,m,C))     continue; 
	//	break;
	} 
	int num=0;
	set<int> tC[MAXN];
	node tH[MAXN];
	int tn,tm,tT[MAXN];
	for (int i=1;i<=m;i++)
		if (find(C0[i],k) || find(C0[i],-k)) num++; 
	if (num>3 && H[k].fx==-1){ //degree>3的先分支 
		copy(H,T,C,tH,tT,tC,n,m,tn,tm); //保护现场
		H[k].fx=0; //值确定
		X[k]=0;
		branch(k+1,n,m,X,maxNum,ans,T,C,C0,H);
		back(H,T,C,tH,tT,tC,n,m,tn,tm); //还原现场
		X[k]=1;
		branch(k+1,n,m,X,maxNum,ans,T,C,C0,H);
		back(H,T,C,tH,tT,tC,n,m,tn,tm);
	}else{
		copy(H,T,C,tH,tT,tC,n,m,tn,tm); //保护现场
		branch(k+1,n,m,X,maxNum,ans,T,C,C0,H); 
		back(H,T,C,tH,tT,tC,n,m,tn,tm); //还原现场
	}
}
int main(){
    freopen("sgen1-unsat-61-100.cnf","r",stdin);
    freopen("output.txt","w",stdout);
    int n,m,maxNum=0;
	set<int> C[MAXN],C0[MAXN];
	int ans[MAXN],X[MAXN],T[MAXN];
    node H[MAXN]; 
    initial(n,m,C0);
    memset(X,-1,sizeof(X));  
	for (int i=0;i<MAXN;i++) H[i].fx=-1;
	for (int i=1;i<=m;i++) C[i]=C0[i];
	memset(T,0,sizeof(T));
	branch(1,n,m,X,maxNum,ans,T,C,C0,H); //将实例转为n3-Max-SAT 
	printf("%d\n",maxNum);
	for (int i=1;i<=n;i++) printf("%d ",ans[i]);
	puts(""); 
    return 0;
}
