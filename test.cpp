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
const int MAXN=505; 
struct node{
	set<int> F;
	int fd;
};
bool find(set<int> C,int x){
	return C.find(x)!=C.end();
}  
void copy(int *tTP,set<int> *C,int *TP,set<int> *tC,int n,int m,int &tn,int &tm){
	tn=n,tm=m;
	for (int i=1;i<MAXN;i++) tTP[i]=TP[i]; 
	for (int i=1;i<MAXN;i++) tC[i]=C[i];
}
void back(int *tTP,set<int> *C,int *TP,set<int> *tC,int &n,int &m,int tn,int tm){
	n=tn,m=tm;
	for (int i=1;i<MAXN;i++) TP[i]=tTP[i]; //注意
	for (int i=1;i<MAXN;i++) C[i]=tC[i];
}
void find3clause(int &c1,int &c2,int &c3,int x,int m,set<int> *C){
	for (c1=1;c1<=m;c1++)
		if (find(C[c1],x)) break;
	for (c2=1;c2<=m;c2++)
		if (find(C[c2],-x)) break;
	for (c3=1;c3<=m;c3++)
		if (c3!=c1 && c3!=c2 && (find(C[c3],x) || find(C[c3],-x))) break;		
}
bool reFrash(int &m,int *X,int *TP,node *H,set<int> *C){
	set<int>::iterator it; 
	for (int i=1;i<=m;i++){ //一个个clause看，是否为空，是否有值确定了
		if (C[i].size()==0){
			C[i]=C[m--];
			return true;
		} 
		for (it=C[i].begin();it!=C[i].end();it++){
			if (TP[abs(*it)]!=0) continue; //要值确定了才
			if (X[abs(*it)]==1){
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
  scanf("%d%d",&n,&m); 
  for (int t=1;t<=m;t++){ 
  	int x;
    C[t].clear();
    while (~scanf("%d",&x) && x){ 
      C[t].insert(x); 
    }
  }  
} 
bool rule1(int n,int &m,int *X,int *TP,node *H,set<int> *C){ 
	set<int>::iterator it;
	bool f=false;
	for (int i=1;i<=m;i++)
		for (it=C[i].begin();it!=C[i].end();it++){
			if (!find(C[i],-*it)) continue; // ~x x 别和X[i]=0,1弄混
			C[i--]=C[m--];
			f=true;
			break;
		} 
	for (int x=1;x<=n;x++){
		if (TP[x]!=-1) continue;  
		int p1=0,p2=0;
		for (int i=1;i<=m;i++){
			if (C[i].size()!=1) continue;
			if (find(C[i],x)) p1=i;  
			if (find(C[i],-x)) p2=i;
		}
		if (!p1 || !p2) continue; //找不到包含~x的unit clause
		C[p1]=C[m--];
		C[p2]=C[m--];
		f=true;
	}
	return f;
}
bool rule2(int n,int &m,int *X,int *TP,node *H,set<int> *C){  //不用管dgree 
	for (int z=1;z<=n;z++){
		if (TP[z]!=-1) continue;
		int p1=0,p2=0,h1=0,h2=0; //p1= x个数   p2= -x个数  h1= x unit  h2= -x unit
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
			TP[z]=0; //z可以直接赋值
			X[z]=1;
			return true;
		}
		if (h2>=p1){
			TP[z]=0; //z可以直接赋值
			X[z]=0;
			return true;
		}
	} 
	return false;
}
bool rule3(int n,int &m,int *X,int *TP,node *H,set<int> *C){ 
	set<int>::iterator it;
	for (int x=1;x<=n;x++){ 
		if (TP[x]!=-1) continue;
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
		TP[x]=1,H[x].F=C[c2],H[x].F.erase(-x); // x由c2得来
		C[c2]=C[m--];
		return true;
	}
	return false;
}
bool rule5(int n,int &m,int *X,int *TP,node *H,set<int> *C){ //在实现的时候只需要让x=1  
	int degree[MAXN];
	set<int>::iterator it;
	memset(degree,0,sizeof(degree));
    for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++)
			degree[abs(*it)]++; 
	for (int x=1;x<=n;x++){  
		if (TP[x]!=-1 || degree[x]!=3) continue;  
		int c1,c2,c3;
		find3clause(c1,c2,c3,x,m,C); //找到这三个clause
		int y=0; 
		for (it=C[c1].begin();it!=C[c1].end();it++){
			if (degree[abs(*it)]!=3) continue;
			if (!find(C[c2],*it) && !find(C[c2],-*it)) continue;
			if (!find(C[c3],*it) && !find(C[c3],-*it)) continue;
			y=abs(*it);
			break;
		}
		if (!y) continue; //是否出问题
		if (find(C[c3],x)){ // x为(2,1)
			TP[x]=0;
			X[x]=1;
		}else{		// x为(1,2)
			TP[x]=0;
			X[x]=0;
		}
		return true;
	}
	return false;
}
bool rule6(int n,int m,int *TP,node *H,set<int> *C){
	int degree[MAXN];
	set<int>::iterator it;
	memset(degree,0,sizeof(degree));
    for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++)
			degree[abs(*it)]++;
	for (int x=1;x<=n;x++){
		if (TP[x]!=-1 || degree[x]!=3) continue;
		int c1,c2,c3,y=0;
		find3clause(c1,c2,c3,x,m,C); //找到这三个clause
		for (it=C[c1].begin();it!=C[c1].end();it++){
			if (*it<0 || degree[*it]!=3) continue; //注意限制y的degree=3
			if (find(C[c2],-*it)){
				y=*it;
				break;
			}
			if (find(C[c3],-x) && find(C[c3],-*it)){ //注意C3必须是包含-x的才可以
				y=*it;
				swap(c2,c3);
				break;
			}
		}
		if (!y) continue; //找不到对应的y
		if (find(C[c3],x)){ //x为(2,1)
			TP[x]=1;
			H[x].F=C[c2],H[x].F.erase(-x);
			C[c2].insert(C[c3].begin(),C[c3].end());
			C[c2].erase(x),C[c2].erase(-x);
			C[c1]=C[m--]; //注意先改clause再删除clause
		}else{				//x为(1,2)
			TP[x]=1;
			H[x].F=C[c1],H[x].F.erase(x);
			C[c1].insert(C[c3].begin(),C[c3].end());
			C[c1].erase(x),C[c1].erase(-x);
			C[c2]=C[m--]; //注意先改clause再删除clause
		}
		return true;
	}
	return false;
}
bool rule7(int n,int &m,int *X,int *TP,node *H,set<int> *C){ 
	int degree[MAXN];
	set<int>::iterator it;
	memset(degree,0,sizeof(degree));
    for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++)
			degree[abs(*it)]++;
	for (int z2=1;z2<=n;z2++){
		if (TP[z2]!=-1 || degree[z2]!=3) continue;
		int c1,c2,c3;
		find3clause(c1,c2,c3,z2,m,C); //找到这三个clause
		//找到了degree=3的z2三个clause c1,c2,c3 
		int z1=0;
		for (it=C[c1].begin();it!=C[c1].end();it++)
			if (find(C[c2],*it)){
				z1=*it;
				break;
			}
		if (!z1) continue;
		if (find(C[c3],z2)){ //(2,1)
			C[c1].erase(z1);
		}else{				 //(1,2)
			C[c2].erase(z1);
		}
		return true;
	}
	return false;
}
bool rule8(int &n,int &m,int *X,int *TP,node *H,set<int> *C){ // (~x',D1,D2) 
	int degree[MAXN];
	set<int>::iterator it;
	memset(degree,0,sizeof(degree));
    for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++)
			degree[abs(*it)]++;
	for (int x=1;x<=n;x++){
		if (TP[x]!=-1 || degree[x]!=3) continue;
		int c1,c2,d1,d2;
		find3clause(c1,c2,d1,x,m,C);
		if (find(C[d1],x)){ //x,y为(2,1)
			swap(c2,d1); 
			int y=0;
			for (it=C[c1].begin();it!=C[c1].end();it++){
				if (*it<0) continue;
				if (find(C[c2],*it)){
					y=*it;
					break;
				}
			}
			if (!y || degree[y]!=3) continue;
			int yc1,yc2;
			find3clause(yc1,d2,yc2,y,m,C);
			H[y].F.clear(),H[y].F.insert(-x);
			H[x].F=C[d1],H[x].F.erase(-x);
			TP[++n]=-1;
			TP[x]=TP[y]=n;  
			H[x].fd=H[y].fd=0;//x,y的值将由n来决定
			C[c1].erase(x),C[c1].erase(y),C[c1].insert(n);
			C[c2].erase(x),C[c2].erase(y),C[c2].insert(n);
			C[d1].insert(C[d2].begin(),C[d2].end());
			C[d1].erase(-x),C[d1].erase(-y),C[d1].insert(-n);
			C[d2]=C[m--];
		}else{				//x,y为(1,2)
			swap(c1,d1);
			set<int>::iterator it;
			int y=0;
			for (it=C[c1].begin();it!=C[c1].end();it++){
				if (*it>0) continue;
				if (find(C[c2],*it)){
					y=*it;
					break;
				}
			}
			if (!y || degree[y]!=3) continue;
			int yc1,yc2;
			find3clause(d2,yc2,yc1,y,m,C); 
			H[y].F.clear(),H[y].F.insert(-x);
			H[x].F.clear();
			for (it=C[d1].begin();it!=C[d1].end();it++){
				if (*it==x) continue;
				H[x].F.insert(-*it);
			} // x= ~D1
			TP[++n]=-1;
			TP[x]=TP[y]=n;  
			H[x].fd=H[y].fd=1;//x,y的值将由n来决定
			C[c1].erase(x),C[c1].erase(y),C[c1].insert(n);
			C[c2].erase(x),C[c2].erase(y),C[c2].insert(n);
			C[d1].insert(C[d2].begin(),C[d2].end());
			C[d1].erase(x),C[d1].erase(y),C[d1].insert(-n);
			C[d2]=C[m--];  
		}
		return true;
	}
	return false;
}
bool rule9(int &m,set<int> *C){
	set<int>::iterator it;
	for (int i=1;i<=m;i++){
		if (C[i].size()!=2) continue;
		int x[2],t=0;
		for (it=C[i].begin();it!=C[i].end();it++) x[t++]=*it;
		int p0=0,p1=0;
		for (int j=1;j<=m;j++){
			if (C[j].size()!=1) continue;
			if (find(C[j],-x[0])) p0=j; 
			if (find(C[j],-x[1])) p1=j;
		}
		if (!p0 || !p1) continue;
		C[i]=C[m--];
		C[p0]=C[m--]; 
		C[p1].insert(-x[0]); //注意
		return true;
	}
	return false;
}
void searchH(int i,int *TP,node *H,int *X){
	set<int>::iterator it;
    if (TP[i]==0) return; //值是确定的
    if (TP[i]==-1){
    	X[i]=TP[i]=0;
    	return;
    }
	if (TP[i]>1){ //其值依赖于H[i].fx与H[i].F的值
		searchH(TP[i],TP,H,X);
		if (X[TP[i]]==0){
			TP[i]=0,X[i]=H[i].fd; //根据rule8规则
			return;
		}
	}
	int t=0;  //只看H[i].F的值
	for (it=H[i].F.begin();it!=H[i].F.end();it++){
		int x=*it;
		searchH(abs(x),TP,H,X);
		if ((x>0 && X[x]==1) || (x<0 && X[-x]==0)){
			t=1;
			break;
		}
	}
	TP[i]=0,X[i]=t; 
} 
void consH(int n,int *TP,node *H,int *tTP,int *X){
	for (int i=1;i<=n;i++) tTP[i]=TP[i];
	for (int i=1;i<=n;i++) searchH(i,TP,H,X);
}
void reTP(int n,int *TP,int *tTP){
	for (int i=1;i<=n;i++) TP[i]=tTP[i];
} 
void branch(int k,int &n,int &m,int n0,int m0,int *X,int &maxNum,int *ans,set<int> *C,set<int> *C0,int *TP,node* H){
	if (k>n || !m){ //分支结束，计算结果
		int tTP[MAXN];
		consH(n0,TP,H,tTP,X); //展开递推关系TP,H
		int t=0; 
		set<int>::iterator it; 
		for (int i=1;i<=m0;i++)
			for (it=C0[i].begin();it!=C0[i].end();it++){ 
				if ((*it>0 && X[*it]==1) || (*it<0 && X[-*it]==0)){
					t++;
					break;
				}
			}
		if (t>maxNum){
			maxNum=t;
			for (int i=1;i<=n0;i++) ans[i]=X[i]; 
		}
		reTP(n0,TP,tTP); //还原TP
		return;
	} 
	while (1){
		while (reFrash(m,X,TP,H,C)); //done
		if (rule1(n,m,X,TP,H,C)) continue; //done
		if (rule2(n,m,X,TP,H,C)) continue; //done
		if (rule3(n,m,X,TP,H,C)) continue; //done
		if (rule5(n,m,X,TP,H,C)) continue; //done
		if (rule6(n,m,TP,H,C))   continue; //done
		if (rule7(n,m,X,TP,H,C)) continue; //done
		if (rule8(n,m,X,TP,H,C)) continue; //done
		if (rule9(m,C))          continue; //done
		break;
	}   
	set<int> tC[MAXN]; 
	int tn,tm,tTP[MAXN]; 
	if (TP[k]==-1){ //值为未知的进行分支
		copy(tTP,C,TP,tC,n,m,tn,tm); //保护现场
		TP[k]=0; //值确定
		X[k]=0;
		branch(k+1,n,m,n0,m0,X,maxNum,ans,C,C0,TP,H);
		back(tTP,C,TP,tC,n,m,tn,tm); //还原现场
		X[k]=1;
		branch(k+1,n,m,n0,m0,X,maxNum,ans,C,C0,TP,H); 
	}else
		branch(k+1,n,m,n0,m0,X,maxNum,ans,C,C0,TP,H);  
}
int main(int argc,char **arg){
    freopen("sgen1-sat-60-100.cnf","r",stdin); 
    freopen("output.txt","w",stdout);
    int n,m,maxNum=0;
	set<int> C[MAXN],C0[MAXN];
	int ans[MAXN],X[MAXN];
	int TP[MAXN]; //TP存变量的状态是 -1 未知  0 为确定值  1 由H[i].F得到  2看H[i].fx之后得到
    node H[MAXN]; 
    initial(n,m,C0);
    memset(X,-1,sizeof(X));  
	memset(TP,-1,sizeof(TP));
	for (int i=1;i<=m;i++) C[i]=C0[i]; 
	branch(1,n,m,n,m,X,maxNum,ans,C,C0,TP,H); 
	printf("%d\n",maxNum);
	for (int i=1;i<=n;i++) printf("%d ",ans[i]);
	puts(""); 
    return 0;
}
