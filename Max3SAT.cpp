#include<iostream>
#include<cstdio>
#include<cstring>
#include<algorithm>
#include<cmath>
#include<map>
#include<time.h>
#include<set>
#include<queue>
#include<stack>
using namespace std;
const int MAXN=1505;
//test 
clock_t TIME[15];
int COUNT[15];

struct node{
	set<int> F;
	int fd;
};
bool find(set<int> C,int x){
//input：clause C and literal x
//output：1 denotes literal x is in C
//      0 denotes literal x is not in C
	return C.find(x)!=C.end();//C.find(x)返回值: x在C中则返回x的位置，否则返回C.end
}
void copy(int *tTP,set<int> *C,int *TP,set<int> *tC,int n,int m,int &tn,int &tm){
//input：把TP的数据存到tTP里去
//output：no exist
	tn=n,tm=m;
	for (int i=1;i<MAXN;i++) tTP[i]=TP[i];
	for (int i=1;i<MAXN;i++) tC[i]=C[i];
}
void back(int *tTP,set<int> *C,int *TP,set<int> *tC,int &n,int &m,int tn,int tm){
//input：把tTP的数据还原到TP里去
//output：no exist
	n=tn,m=tm;
	for (int i=1;i<MAXN;i++) TP[i]=tTP[i]; //注意
	for (int i=1;i<MAXN;i++) C[i]=tC[i];
}
void find3clause(int &c1,int &c2,int &c3,int x,int c[MAXN][3]){
//input：找到degree 为3的variable x的3个子句
//output：0
	c1=c[x][0],c2=c[x][1],c3=c[x][2];
}
bool reNew(int &m,int *X,int *TP,node *H,set<int> *C,int &Upbound){
//input： 子句数m X是存当前赋值， TP是每个X的当前状态， H是递推关系， C是当前所有的子句
//output：1 至少做了一次操作：{1.子句为空，去掉子句；2.如果一个子句的字符值为1，去掉该子句； 如果为0,删去该子句中的字符}
//      0 无操作
	set<int>::iterator it;
	for (int i=1;i<=m;i++){ //一个个clause看，是否为空，是否有值确定了
		if (C[i].size()==0){
			C[i]=C[m--]; 
			Upbound--;
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
//input：读入数据
  char s[100];
  while (~scanf("%s",s)){
  	  if (strlen(s)!=1) continue;
  	  if (s[0]=='p') break;
  }
  scanf("%s",s);
  scanf("%d%d",&n,&m);
  for (int t=1;t<=m;t++){
  	int x;
    C[t].clear();
    while (~scanf("%d",&x) && x){
      C[t].insert(x);
    }
  }
}
bool rule1_1(int n,int &m,int *X,int *TP,node *H,set<int> *C){  
	set<int>::iterator it;
	bool f=false;
	for (int i=1;i<=m;i++){
		int p[MAXN];
		memset(p,0,sizeof(p));
		for (it=C[i].begin();it!=C[i].end();it++){ 
			int x=*it;
			if (x>0) p[x]++;
			    else x=-x,p[x]--;
			if (!p[x]){
				C[i--]=C[m--]; 
				f=true;
				break;
			}
		}
	}
	//if (f) puts("rule1.1");
	return f;
}
bool rule1_2(int n,int &m,int *X,int *TP,node *H,set<int> *C,int &Upbound){
	bool f=false;
	int p[MAXN][2];
	memset(p,0,sizeof(p));
	for (int i=1;i<=m;i++){
		if (C[i].size()!=1) continue;
		int x=*C[i].begin();
		if (x>0) p[x][0]=i;
		    else p[-x][1]=i; 
	}
	for (int x=1;x<=n;x++){
		if (TP[x]!=-1) continue;
		if (!p[x][0] || !p[x][1]) continue;
		if (p[x][0]>p[x][1])
			C[p[x][0]]=C[m--],C[p[x][1]]=C[m--];
		else
			C[p[x][1]]=C[m--],C[p[x][0]]=C[m--];
		Upbound--;
		f=true;
	} 
	//if (f) puts("rule1.2");
	return f;
}
bool rule2(int n,int &m,int *X,int *TP,node *H,set<int> *C){  //不用管dgree
	int p1[MAXN],p2[MAXN],h1[MAXN],h2[MAXN],x;
	bool f=false;
	set<int>::iterator it;
	memset(p1,0,sizeof(p1));
	memset(p2,0,sizeof(p2));
	memset(h1,0,sizeof(h1));
	memset(h2,0,sizeof(h2));
	for (int i=1;i<=m;i++){
		if (C[i].size()==1){
			x=*C[i].begin(); 
			if (x>0) h1[x]++;
			    else h2[-x]++; 
		}
		for (it=C[i].begin();it!=C[i].end();it++){
			x=*it;
			if (x>0) p1[x]++;
			    else p2[-x]++; 			
		}
	}
	for (int z=1;z<=n;z++){
		if (TP[z]!=-1) continue;
		if (h1[z]>=p2[z]){
			TP[z]=0;
			X[z]=1;
			f=true;
		}else
		if (h2[z]>=p1[z]){
			TP[z]=0;
			X[z]=0;
			f=true;
		}
	}
    return f; 
}
bool rule3(int n,int &m,int *X,int *TP,node *H,set<int> *C){
	int degree[MAXN],c[MAXN][2];
	set<int>::iterator it;
	memset(degree,0,sizeof(degree));
    for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++)
			degree[abs(*it)]++;
    memset(c,0,sizeof(c));
    for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++){
    		int x=*it;
    		if (degree[abs(x)]!=2) continue;
    		if (x>0) c[x][0]=i;
    		   else  c[-x][1]=i; 
    	} 
	for (int x=1;x<=n;x++){
		if (TP[x]!=-1 || degree[x]!=2) continue;
		int c1=c[x][0],c2=c[x][1]; 
		C[c1].insert(C[c2].begin(),C[c2].end()); //合并set
		C[c1].erase(x),C[c1].erase(-x);
		TP[x]=1,H[x].F=C[c2],H[x].F.erase(-x);// x由c2得来
		C[c2]=C[m--]; //删掉c2
		return true;
	}
	return false;
}
bool rule5(int n,int &m,int *X,int *TP,node *H,set<int> *C){ //在实现的时候只需要让x=1
	int degree[MAXN],c[MAXN][3];
	set<int>::iterator it; 
	memset(degree,0,sizeof(degree));
    for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++)
			degree[abs(*it)]++;
    memset(c,0,sizeof(c));
    for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++){
    		int x=*it;
    		if (degree[abs(x)]!=3) continue;
    		if (x>0){
    			if (!c[x][0]) c[x][0]=i;
    			        else  c[x][2]=i;
    		}else{
    			x=-x;
    			if (!c[x][1]) c[x][1]=i;
    			        else  c[x][2]=i;
    		}
    	} 
	for (int x=1;x<=n;x++){
		if (TP[x]!=-1 || degree[x]!=3) continue;
		int c1,c2,c3;
		find3clause(c1,c2,c3,x,c); //找到这三个clause
		int y=0;
		for (it=C[c1].begin();it!=C[c1].end();it++){
			if (degree[abs(*it)]!=3 || TP[abs(*it)]!=-1) continue; //是否出问题
			if (*it==x) continue;
			if (!find(C[c2],*it) && !find(C[c2],-*it)) continue;
			if (!find(C[c3],*it) && !find(C[c3],-*it)) continue;
			y=abs(*it);
			break;
		}
		if (!y) continue;
		if (find(C[c3],x)){ // x为(2,1)
			TP[x]=0;
			X[x]=1;
		}else{		// x为(1,2)
			TP[x]=0;
			X[x]=0;
		}
		//puts("Rule 5");
		return true;
	}
	return false;
}
bool rule6(int n,int &m,int *TP,node *H,set<int> *C){ //注意m为变参
	int degree[MAXN],c[MAXN][3];
	set<int>::iterator it; 
	memset(degree,0,sizeof(degree));
    for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++)
			degree[abs(*it)]++;
    memset(c,0,sizeof(c));
    for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++){
    		int x=*it;
    		if (degree[abs(x)]!=3) continue;
    		if (x>0){
    			if (!c[x][0]) c[x][0]=i;
    			        else  c[x][2]=i;
    		}else{
    			x=-x;
    			if (!c[x][1]) c[x][1]=i;
    			        else  c[x][2]=i;
    		}
    	} 
	for (int x=1;x<=n;x++){
		if (TP[x]!=-1 || degree[x]!=3) continue;
		int c1,c2,c3,y=0;
		find3clause(c1,c2,c3,x,c); //找到这三个clause
		for (it=C[c1].begin();it!=C[c1].end();it++){
			if (*it==x) continue; //注意
			if (TP[abs(*it)]!=-1) continue; //需要么
    	//	if (degree[abs(*it)]!=3) continue; //注意限制y的degree=3  *it的正负不用限制
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
			TP[x]=1; //x的值由c2推出
			H[x].F=C[c2],H[x].F.erase(-x);
			C[c2].insert(C[c3].begin(),C[c3].end());
			C[c2].erase(x),C[c2].erase(-x);
			if (c1>c3) //多个删除注意顺序
				C[c1]=C[m--],C[c3]=C[m--]; //注意先改clause再删除clause
			else
				C[c3]=C[m--],C[c1]=C[m--];
		}else{				//x为(1,2)
			TP[x]=1; //x的值由c1推出
			H[x].F=C[c1],H[x].F.erase(x);
			C[c1].insert(C[c3].begin(),C[c3].end());
			C[c1].erase(x),C[c1].erase(-x);
			if (c2>c3)  //多个删除注意顺序
				C[c2]=C[m--],C[c3]=C[m--]; //注意先改clause再删除clause
			else
				C[c3]=C[m--],C[c2]=C[m--];
		}  
		//puts("Rule 6");
		return true;
	}
	return false;
}
bool rule7(int n,int &m,int *X,int *TP,node *H,set<int> *C){
	int degree[MAXN],c[MAXN][3];
	set<int>::iterator it; 
	memset(degree,0,sizeof(degree));
    for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++)
			degree[abs(*it)]++;
    memset(c,0,sizeof(c));
    for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++){
    		int x=*it;
    		if (degree[abs(x)]!=3) continue;
    		if (x>0){
    			if (!c[x][0]) c[x][0]=i;
    			        else  c[x][2]=i;
    		}else{
    			x=-x;
    			if (!c[x][1]) c[x][1]=i;
    			        else  c[x][2]=i;
    		}
    	} 
	for (int z2=1;z2<=n;z2++){
		if (TP[z2]!=-1 || degree[z2]!=3) continue;
		int c1,c2,c3;
		find3clause(c1,c2,c3,z2,c); //找到这三个clause
		//找到了degree=3的z2三个clause c1,c2,c3
		int z1=0;
		for (it=C[c1].begin();it!=C[c1].end();it++)
			if (find(C[c2],*it) && TP[abs(*it)]==-1){ //是否需要限制TP[*it]
				z1=*it;
				break;
			}
		if (!z1) continue;
		if (find(C[c3],z2)){ //z2为(2,1)
			C[c1].erase(z1);
		}else{				 //z2为(1,2)
			C[c2].erase(z1);
		}
		//puts("Rule 7");
		return true;
	}
	return false;
}
bool rule8(int &n,int &m,int *X,int *TP,node *H,set<int> *C){ // (~x',D1,D2)
	int degree[MAXN],c[MAXN][3];
	set<int>::iterator it; 
	memset(degree,0,sizeof(degree));
    for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++)
			degree[abs(*it)]++;
    memset(c,0,sizeof(c));
    for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++){
    		int x=*it;
    		if (degree[abs(x)]!=3) continue;
    		if (x>0){
    			if (!c[x][0]) c[x][0]=i;
    			        else  c[x][2]=i;
    		}else{
    			x=-x;
    			if (!c[x][1]) c[x][1]=i;
    			        else  c[x][2]=i;
    		}
    	} 
	for (int x=1;x<=n;x++){
		if (TP[x]!=-1 || degree[x]!=3) continue;
		int c1,c2,d1,d2;
		find3clause(c1,c2,d1,x,c);
		if (find(C[d1],x)) swap(c2,d1); // x (2,1)
		              else swap(c1,d1); // x (1,2)
		int y=0;
		for (it=C[c1].begin();it!=C[c1].end();it++){
			if (TP[abs(*it)]!=-1 || degree[abs(*it)]!=3) continue;
			if (abs(*it)==x) continue;
			if (find(C[c2],*it)){
				y=abs(*it); //y满足:  y未赋值  y的degree=3  y!=x
				break;
			}
		}
		if (!y) continue; //找不到对应的y   
		find3clause(c1,c2,d2,y,c);
		if (find(C[d2],y)) swap(c2,d2);
		              else swap(c1,d2);
		TP[++n]=-1;
		TP[x]=TP[y]=n;
		if (find(C[d1],-x)){
			H[x].fd=0;
			H[x].F=C[d1],H[x].F.erase(-x);
		}else{
			H[x].fd=1;
			H[x].F=C[d2]; 
			if (find(C[d2],y)) H[x].F.erase(y);
			              else H[x].F.erase(-y);
		}
		if (find(C[d2],-y)){
			H[y].fd=0;
			H[y].F.clear(),H[y].F.insert(-x);
		}else{
			H[y].fd=1;
			H[y].F.clear(),H[y].F.insert(x);
		}
		if (find(C[c1],x)) C[c1].erase(x);
		              else C[c1].erase(-x);
		if (find(C[c2],x)) C[c2].erase(x);
		              else C[c2].erase(-x);
		if (find(C[d1],x)) C[d1].erase(x);
		              else C[d1].erase(-x);
		if (find(C[d2],y)) C[d2].erase(y);
		              else C[d2].erase(-y);		
		C[d1].insert(C[d2].begin(),C[d2].end());
		C[d2]=C[m--];
		C[c1].insert(n),C[c2].insert(n),C[d1].insert(n); 
		return true;
	} 
	return false;
}
bool rule9(int &m,int *TP,set<int> *C,int &Upbound){
	int p[MAXN][2];
	set<int>::iterator it;
	memset(p,0,sizeof(p));
	for (int i=1;i<=m;i++){
		if (C[i].size()!=1) continue;
		int x=*C[i].begin();
		if (x>0) p[x][0]=i;
		    else p[-x][1]=i;
	} 
	for (int i=1;i<=m;i++){
		if (C[i].size()!=2) continue;
		int x[2],t=0;
		for (it=C[i].begin();it!=C[i].end();it++) x[t++]=*it;
		if (TP[abs(x[0])]!=-1 || TP[abs(x[1])]!=-1) continue;
		int p0,p1;
		if (x[0]>0) p0=p[x[0]][1];
		       else p0=p[-x[0]][0];
		if (x[1]>0) p1=p[x[1]][1];
			   else p1=p[-x[1]][0];
		if (!p0 || !p1) continue;
		C[p1].insert(-x[0]); //先插入 后删除
		if (i>p0)
			C[i]=C[m--],C[p0]=C[m--];
		else
			C[p0]=C[m--],C[i]=C[m--];
		Upbound--;
		return true;
	}
	return false;
} 
 
void searchH(int i,int n,int *TP,node *H,int *X){
//展开递推关系
//判断第i个变量的值, 通过H
//input：i is the existing extentable variableclause C and literal x
//output：1 denotes literal x is in C
//      0 denotes literal x is not in C
	set<int>::iterator it;
    if (TP[i]==0) return; //值是确定的 
	if (TP[i]>1){ //其值依赖于H[i].fx与H[i].F的值
		searchH(TP[i],n,TP,H,X);
		if (X[TP[i]]==0){    //根据rule8规则
			TP[i]=0,X[i]=H[i].fd; //根据rule8规则
			return;
		}
	}
	int t=0;  //只看H[i].F的值
	for (it=H[i].F.begin();it!=H[i].F.end();it++){
		int x=*it;
		searchH(abs(x),n,TP,H,X);
		if ((x>0 && X[x]==1) || (x<0 && X[-x]==0)){
			t=1;
			break;
		}
	}
	TP[i]=0,X[i]=t;
}
void consH(int n,int *TP,node *H,int *tTP,int *X){
//根据H,把X的值全构造出来
//input：clause C and literal x
//output：1 denotes literal x is in C
//      0 denotes literal x is not in C
	for (int i=1;i<=n;i++) tTP[i]=TP[i]; 
	for (int i=1;i<=n;i++) searchH(i,n,TP,H,X);
}
void reTP(int n,int *TP,int *tTP){
//还原tp
	for (int i=1;i<=n;i++) TP[i]=tTP[i];
}
void branch(int &n,int &m,int n0,int m0,int *X,int &maxNum,int *ans,set<int> *C,set<int> *C0,int *TP,node* H,int Upbound){
	COUNT[0]++;
	while (1){
		clock_t start;
		start=clock();
		while (reNew(m,X,TP,H,C,Upbound)); //done
		TIME[0]+=clock()-start;
		if (Upbound<=maxNum) return;
		start=clock();
		if (rule1_1(n,m,X,TP,H,C)) { TIME[1]+=clock()-start; COUNT[1]++; continue; } //done
		TIME[1]+=clock()-start; 
		start=clock();
		if (rule1_2(n,m,X,TP,H,C,Upbound)) { TIME[10]+=clock()-start; COUNT[4]++; continue; } //done
		TIME[10]+=clock()-start; 
		start=clock();
		if (rule2(n,m,X,TP,H,C)) { TIME[2]+=clock()-start; COUNT[2]++; continue; } //done
		TIME[2]+=clock()-start; 
		start=clock();
		if (rule3(n,m,X,TP,H,C)) { TIME[3]+=clock()-start; COUNT[3]++; continue; } //done
		TIME[3]+=clock()-start; 
		start=clock();
		if (rule5(n,m,X,TP,H,C)) { TIME[5]+=clock()-start; COUNT[5]++; continue; } //done
		TIME[5]+=clock()-start; 
		start=clock();
		if (rule6(n,m,TP,H,C))   { TIME[6]+=clock()-start; COUNT[6]++; continue; } //done
		TIME[6]+=clock()-start; 
		start=clock();
		if (rule7(n,m,X,TP,H,C)) { TIME[7]+=clock()-start; COUNT[7]++; continue; } //done
		TIME[7]+=clock()-start; 
		start=clock();
		if (rule8(n,m,X,TP,H,C)) { TIME[8]+=clock()-start; COUNT[8]++; continue; } //done
		TIME[8]+=clock()-start; 
		start=clock();
		if (rule9(m,TP,C,Upbound)) { TIME[9]+=clock()-start; COUNT[9]++; continue; } //done
		TIME[9]+=clock()-start; 
		break;
	}
	set<int> tC[MAXN];
	int tn,tm,tTP[MAXN],degree[MAXN],D[MAXN],k=0;
	set<int>::iterator it;
	memset(degree,0,sizeof(degree));
    for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++)
			degree[abs(*it)]++;	
	memset(D,0,sizeof(D));
	for (int i=1;i<=n;i++) D[i]=degree[i]*2;
	for (int i=1;i<=m;i++){ // 
		int d3=0,d4=0;
		for (it=C[i].begin();it!=C[i].end();it++){
			if (degree[abs(*it)]==3) d3+=2;
			if (degree[abs(*it)]==4) d4++;
		}
		for (it=C[i].begin();it!=C[i].end();it++)
			D[abs(*it)]+=d3+d4;
	}
	for (int i=1;i<=n;i++)
		if (TP[i]==-1 && D[k]<D[i]) k=i; 
	if (k){
		copy(tTP,C,TP,tC,n,m,tn,tm); //保护现场
		TP[k]=0; //值确定
		X[k]=0;
		branch(n,m,n0,m0,X,maxNum,ans,C,C0,TP,H,Upbound);
		back(tTP,C,TP,tC,n,m,tn,tm); //还原现场
		TP[k]=0; //----大错点----不加则死循环---
		X[k]=1;
		branch(n,m,n0,m0,X,maxNum,ans,C,C0,TP,H,Upbound);
		back(tTP,C,TP,tC,n,m,tn,tm); //还原现场
		return;
	}
	consH(n0,TP,H,tTP,X); //展开递推关系TP,H
	int t=0; 
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
	reTP(n0,TP,tTP);
	return;
}
int main(int argc,char **arg){
    freopen(arg[1],"r",stdin);
    //freopen("output.txt","w",stdout);
    int n,m,n0,maxNum=0;
    clock_t start,finish; 
    start=clock();
	set<int> C[MAXN],C0[MAXN];
	int ans[MAXN],X[MAXN];
	int TP[MAXN]; //TP存变量的状态是 -1 未知  0 为确定值  1 由H[i].F得到  2看H[i].fx之后得到
    node H[MAXN];
    initial(n,m,C0);
    n0=n; 
    memset(TP,-1,sizeof(TP));
	for (int i=1;i<=m;i++) C[i]=C0[i]; 
	memset(X,-1,sizeof(X));
    memset(TIME,0,sizeof(TIME));
    memset(COUNT,0,sizeof(COUNT));
	branch(n,m,n,m,X,maxNum,ans,C,C0,TP,H,m);
	puts("---------------------------------------------");
	printf("%d\n",maxNum);
	for (int i=1;i<=n0;i++){
        if(ans[i]) printf("%d ", i);
        else printf("%d ",-i); 
    }
	puts("\n");
	finish=clock();
	printf("Total time is %.5lf seconds.\n",(double)(finish - start)/CLOCKS_PER_SEC);
	printf("reNew    : %.5lf seconds.\n",(double)TIME[0]/CLOCKS_PER_SEC);
	printf("Rule 1.1 : %.5lf seconds.\n",(double)TIME[1]/CLOCKS_PER_SEC);
	printf("Rule 1.2 : %.5lf seconds.\n",(double)TIME[10]/CLOCKS_PER_SEC);
	for (int i=2;i<=9;i++){
		if (i==4) continue;
		printf("Rule %d   : %.5lf seconds.\n",i,(double)TIME[i]/CLOCKS_PER_SEC);
	}
	puts("");
	printf("NB_Branch  : %d\n",COUNT[0]);
	printf("NB_Rule 1.1: %d\n",COUNT[1]);
	printf("NB_Rule 1.2: %d\n",COUNT[4]);
	for (int i=2;i<=9;i++){
		if (i==4) continue;
		printf("NB_Rule %d  : %d\n",i,COUNT[i]);
	}
    return 0;
}
