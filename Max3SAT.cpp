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
const int NB_V=2505;
const int NB_C=4505;
//test 
clock_t TIME[25];
int COUNT[25];

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
void back(int *TP,set<int> *C,int &n,int &m,map<int,int> &tTP,map<int,set<int> > &tC,int tn,int tm){
//input：把tTP的数据还原到TP里去
//output：no exist     
	for (map<int,int>::iterator it=tTP.begin();it!=tTP.end();it++)
		TP[it->first]=it->second; 
    for (map<int,set<int> >::iterator it=tC.begin();it!=tC.end();it++) 
		C[it->first]=it->second; 
	n=tn;
	m=tm;
}
void find3clause(int &c1,int &c2,int &c3,int x,vector<int> LC[][2]){
//input：找到degree 为3的variable x的3个子句
//output：0
	c1=LC[x][0][0],c2=LC[x][1][0];
	if (LC[x][0].size()!=1) c3=LC[x][0][1];
	                   else c3=LC[x][1][1]; 
}
void reNew(int &m,int *X,int *TP,node *H,set<int> *C,int &Upbound,map<int,set<int> > &tC){
//input： 子句数m X是存当前赋值， TP是每个X的当前状态， H是递推关系， C是当前所有的子句
//output：1 至少做了一次操作：{1.子句为空，去掉子句；2.如果一个子句的字符值为1，去掉该子句； 如果为0,删去该子句中的字符}
//      0 无操作
	set<int>::iterator it; 
	for (int i=1;i<=m;i++){ //一个个clause看，是否为空，是否有值确定了
		if (C[i].size()==0){
			if (tC.find(i)==tC.end())
			    tC[i]=C[i];//----纪录改变
			C[i--]=C[m--]; 
			Upbound--;
			continue;
		}
		for (it=C[i].begin();it!=C[i].end();it++){
			if (TP[abs(*it)]!=0) continue; //要值确定了才
			if (tC.find(i)==tC.end())
			    tC[i]=C[i];//----纪录改变
			if (X[abs(*it)]==1){ 
				if (*it>0) C[i--]=C[m--];
					  else C[i--].erase(*it);
			}else{
				if (*it<0) C[i--]=C[m--];
					  else C[i--].erase(*it);
			}
			break;
		}
	}  
}
void Output(int maxNum){ 
	//system("clear");
	printf("MaxNum = %d\n",maxNum);
	printf("NB_Branch   : %d\n",COUNT[0]); 
	printf("NB_Rule 1.2 : %d\n",COUNT[4]);
	for (int i=2;i<=8;i++){
		if (i==4 || i==5) continue;
		printf("NB_Rule %d   : %d\n",i,COUNT[i]);
	} 
	puts("#################################");
}
void Output1(int x,set<int> *C,vector<int> LC[][2]){
	set<int>::iterator it;
	for (int i=0;i<LC[x][0].size();i++){
		printf("(");
		int c1=LC[x][0][i];
		for (it=C[c1].begin();it!=C[c1].end();it++)
			printf("%d ",*it);
			puts(")");
		}
	for (int i=0;i<LC[x][1].size();i++){
		printf("(");
		int c1=LC[x][1][i];
		for (it=C[c1].begin();it!=C[c1].end();it++)
			printf("%d ",*it);
			puts(")");				
	}
	puts("--------");
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
bool rule1_1(int &m,set<int> *C){  
	set<int>::iterator it;
	bool f=false; 
	for (int i=1;i<=m;i++){
		int p[NB_V];
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
bool rule1_2(int n,int &m,int *X,int *TP,node *H,set<int> *C,int &Upbound,map<int,set<int> > &tC){
	bool f=false;
	int p[NB_V][2]; 
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
		if (tC.find(p[x][0])==tC.end())
			 tC[p[x][0]]=C[p[x][0]];//----纪录改变 
		if (tC.find(p[x][1])==tC.end())
			 tC[p[x][1]]=C[p[x][1]];//----纪录改变 
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
int p1[NB_V],p2[NB_V],h1[NB_V],h2[NB_V];
bool rule2(int n,int &m,int *X,int *TP,node *H,set<int> *C,map<int,int> &tTP){  //不用管dgree
	int x; 
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
			if (tTP.find(z)==tTP.end())
				tTP[z]=TP[z]; //----纪录改变
			TP[z]=0;
			X[z]=1;
			f=true;
		}else
		if (h2[z]>=p1[z]){
			if (tTP.find(z)==tTP.end())
				tTP[z]=TP[z]; //----纪录改变
			TP[z]=0;
			X[z]=0;
			f=true;
		}
	}
    return f; 
}
bool rule3(int n,int &m,int *X,int *TP,node *H,set<int> *C,vector<int> LC[][2],map<int,int> &tTP,map<int,set<int> > &tC){  
	for (int x=1;x<=n;x++){
		if (TP[x]!=-1 || LC[x][0].size()!=1 || LC[x][1].size()!=1) continue;
		int c1=LC[x][0][0],c2=LC[x][1][0]; 
		if (tC.find(c1)==tC.end())
			tC[c1]=C[c1]; //----纪录改变
		if (tC.find(c2)==tC.end())
			tC[c2]=C[c2]; //----纪录改变
		if (tTP.find(x)==tTP.end())
			tTP[x]=TP[x]; //----纪录改变
		C[c1].insert(C[c2].begin(),C[c2].end()); //合并set
		C[c1].erase(x),C[c1].erase(-x);
		TP[x]=1,H[x].F=C[c2],H[x].F.erase(-x);// x由c2得来
		C[c2]=C[m--]; //删掉c2
		return true;
	}
	return false;
} 
void rule6(int &n,int &m,int *TP,node *H,set<int> *C,int *X,vector<int> LC[][2],map<int,set<int> > &tC,vector<int> &LX){ //注意m为变参
	set<int>::iterator it;    
	vector<int>::iterator t1,p1,p2;
	//-----rule6_1
	for (t1=LX.begin();t1!=LX.end();t1++){
		int x=*t1;
		if (LC[x][0].size()==1){  //  x为(1,i)
			int c1,c2=0;
			c1=LC[x][0][0];
			for (it=C[c1].begin();it!=C[c1].end();it++){ 
				int y=*it,k=1;
				if (y>0) k=0;
				    else y=-y; 
				for (p1=LC[x][1].begin(),p2=LC[y][k].begin();p1!=LC[x][1].end() && p2!=LC[y][k].end();){ 
					if (*p1==*p2){
						c2=*p1;
						break;
					}
					if (*p1<*p2) p1++;
					        else p2++;
				} 
				if (c2) break;
			}
			if (!c2) continue;  
			if (tC.find(c2)==tC.end())
				tC[c2]=C[c2]; //----纪录改变  
			C[c2].erase(*it);   
			COUNT[6]++; 
		}else{  //  x为(i,1)
			int c1=0,c2;
			c2=LC[x][1][0];
			for (it=C[c2].begin();it!=C[c2].end();it++){ 
				int y=*it,k=1;
				if (y>0) k=0;
				    else y=-y;
				for (p1=LC[x][0].begin(),p2=LC[y][k].begin();p1!=LC[x][0].end() && p2!=LC[y][k].end();){  
					if (*p1==*p2){
						c1=*p1;
						break;
					}
					if (*p1<*p2) p1++;
					        else p2++;
				} 
				if (c1) break;
			}
			if (!c1) continue; 
			if (tC.find(c1)==tC.end())
				tC[c1]=C[c1]; //----纪录改变  tC[c1]=C[c1]; //----纪录改变  
			C[c1].erase(*it);  
			COUNT[6]++; 
		} 
	} 
    //-----rule6_2
	for (t1=LX.begin();t1!=LX.end();t1++){
		int x=*t1;
		if (LC[x][0].size()==1){  // x为(1,i)
			int c1=0,D;
			D=LC[x][0][0];
			for (it=C[D].begin();it!=C[D].end();it++){
				int y=*it,k=0;
				if (y>0) k=1;
				    else y=-y; 
				if (y==x) continue;
				for (p1=LC[x][1].begin(),p2=LC[y][k].begin();p1!=LC[x][1].end() && p2!=LC[y][k].end();){ 
					if (*p1==*p2 && (LC[x][1].size()==2 || C[*p1].size()>2)){
						c1=*p1;
						break;
					} 
					if (*p1<*p2) p1++;
					       else  p2++;
				}
				if (c1) break; 
			}
			if (!c1) continue;
			if (tC.find(c1)==tC.end())
				tC[c1]=C[c1]; //----纪录改变  
			if (LC[x][1].size()==2) 
				C[c1]=C[m--];
			else{
				C[c1].clear();
				C[c1].insert(-x),C[c1].insert(-*it);
			} 
			COUNT[6]++; 
		}else{ // x为(i,1)
			int c1=0,D;
			D=LC[x][1][0];
			for (it=C[D].begin();it!=C[D].end();it++){
				int y=*it,k=0;
				if (y>0) k=1;
				    else y=-y; 
				if (y==x) continue;
				for (p1=LC[x][0].begin(),p2=LC[y][k].begin();p1!=LC[x][0].end() && p2!=LC[y][k].end();){ 
					if (*p1==*p2 && (LC[x][0].size()==2 || C[*p1].size()>2)){
						c1=*p1;
						break;
					} 
					if (*p1<*p2) p1++;
					       else  p2++;
				}
				if (c1) break; 
			}
			if (!c1) continue;
			if (tC.find(c1)==tC.end())
				tC[c1]=C[c1]; //----纪录改变  
			if (LC[x][0].size()==2) 
				C[c1]=C[m--];
			else{
				C[c1].clear();
				C[c1].insert(-x),C[c1].insert(-*it);
			} 
			COUNT[6]++; 
		}
	} 
}
bool rule7(int &n,int &m,int *TP,node *H,set<int> *C,int *X,vector<int> LC[][2],map<int,set<int> > &tC,map<int,int> &tTP,vector<int> &LX){ //注意m为变参
	set<int>::iterator it;     
	//-----rule7 
	for (int x=1;x<=n;x++){
		if (TP[x]!=-1) continue;  
		if (LC[x][0].size()==1){ // x为(1,i)   x=x' y
			int c1,ci,D1,k,y;
		    c1=LC[x][1][0],D1=LC[x][0][0];
			for (it=C[c1].begin();it!=C[c1].end();it++){
				y=*it;
				if (y==-x) continue;  //注意
				for (k=LC[x][1].size()-1;k>=1;k--){
					ci=LC[x][1][k];
					if (!find(C[ci],y)) break;
				}
				if (k==0) break; 
			}
	        if (it==C[c1].end()) continue;   
		    TP[++n]=-1; //加入新点x'
		    for (k=LC[x][1].size()-1;k>=0;k--){
		    	ci=LC[x][1][k];
				if (tC.find(ci)==tC.end())
					tC[ci]=C[ci]; //----纪录改变  
		    	C[ci].erase(-x),C[ci].erase(y);
		    	C[ci].insert(-n);
		    }
			if (tC.find(D1)==tC.end())
				tC[D1]=C[D1]; //----纪录改变  
		    C[D1].erase(x);
		    C[D1].insert(n),C[D1].insert(y);
		    if (tTP.find(x)==tTP.end())
		    	tTP[x]=TP[x]; 
		    TP[x]=1;
		    H[x].F.clear();
		    H[x].F.insert(n),H[x].F.insert(y);
		    return true;  
		}else
		if (LC[x][1].size()==1){ // x为(i,1)
			int c1,ci,D1,k,y;
			c1=LC[x][0][0],D1=LC[x][1][0];
			for (it=C[c1].begin();it!=C[c1].end();it++){
				y=*it;
				if (y==x) continue;  //注意
				for (k=LC[x][0].size()-1;k>=1;k--){
					ci=LC[x][0][k];
					if (!find(C[ci],y)) break;
				}
				if (k==0) break; 
			}
			if (it==C[c1].end()) continue;  
			TP[++n]=-1; //加入新点x'
			for (k=LC[x][0].size()-1;k>=0;k--){
				ci=LC[x][0][k];
				if (tC.find(ci)==tC.end())
					tC[ci]=C[ci]; //----纪录改变  
				C[ci].erase(x),C[ci].erase(y);
				C[ci].insert(n);
			}
			if (tC.find(D1)==tC.end())
				tC[D1]=C[D1]; //----纪录改变  
			C[D1].erase(-x);
			C[D1].insert(-n),C[D1].insert(y);
			if (tTP.find(x)==tTP.end())
				tTP[x]=TP[x]; 
			TP[x]=n,H[x].fd=0;
			H[x].F.clear();
			H[x].F.insert(-n),H[x].F.insert(-y);
			return true;
		} 
	}   
	return false;
}
bool rule8(int &m,int *TP,set<int> *C,int &Upbound,map<int,set<int> > &tC){
	int p[NB_V][2];
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
		if (tC.find(p1)==tC.end())
			tC[p1]=C[p1]; //----纪录改变  
		if (tC.find(i)==tC.end())
			tC[i]=C[i]; //----纪录改变  
	    if (tC.find(p0)==tC.end())
			tC[p0]=C[p0]; //----纪录改变  
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
void searchH(int i,int n,int *TP,node *H,int *X,map<int,int> &tTP){
//展开递推关系
//判断第i个变量的值, 通过H
//input：i is the existing extentable variableclause C and literal x
//output：1 denotes literal x is in C
//      0 denotes literal x is not in C
	set<int>::iterator it; 
    if (TP[i]==0) return; //值是确定的     
	if (tTP.find(i)==tTP.end())
		tTP[i]=TP[i]; //---纪录变化
	if (TP[i]>1){ //其值依赖于H[i].fx与H[i].F的值
		searchH(TP[i],n,TP,H,X,tTP);
		if (X[TP[i]]==0){    //根据rule8规则
			TP[i]=0,X[i]=H[i].fd; //根据rule8规则
			return;
		}
	}
	int t=0;  //只看H[i].F的值
	for (it=H[i].F.begin();it!=H[i].F.end();it++){
		int x=*it;
		searchH(abs(x),n,TP,H,X,tTP);
		if ((x>0 && X[x]==1) || (x<0 && X[-x]==0)){
			t=1;
			break;
		}
	} 
	TP[i]=0,X[i]=t;
}
void consH(int n,int *TP,node *H,int *X,map<int,int> &tTP){
//根据H,把X的值全构造出来
//input：clause C and literal x
//output：1 denotes literal x is in C
//      0 denotes literal x is not in C  
	for (int i=1;i<=n;i++) searchH(i,n,TP,H,X,tTP);
}
void reUB(int n,int m,set<int> *C,int &Upbound){
	int unit[n+5][2];
	set<int>::iterator it;
	memset(unit,0,sizeof(unit));
	for (int i=1;i<=m;i++){
		if (C[i].size()!=1) continue;
		int x=*C[i].begin();
		if (x>0) unit[x][0]++;   //  为正的unit个数
		    else unit[-x][1]++;  //  为负的unit个数
	}
	for (int i=1;i<=m;i++){
		for (it=C[i].begin();it!=C[i].end();it++){
			int x=*it;
			if (x>0){
				if (!unit[x][1]) break;
			}else{
				if (!unit[-x][0]) break;
			}
		}
		if (it!=C[i].end()) continue;
		Upbound--;
		for (it=C[i].begin();it!=C[i].end();it++){
			int x=*it;
			if (x>0) unit[x][1]--;
				else unit[-x][0]--;
		}
	}
}
void getLC(int n0,int m,set<int> *C,vector<int> LC[][2],int *TP,bool &D3,vector<int> &LX){
	set<int>::iterator it;
	int n=0,DM=0;
	for (int i=1;i<=n0;i++)
		if (TP[i]==-1) n++;
	for (int i=1;i<=n0;i++) LC[i][0].clear(),LC[i][1].clear();
   	for (int i=1;i<=m;i++)
     	for (it=C[i].begin();it!=C[i].end();it++){
     		int x=*it;
			DM++;
			if (x>0) LC[x][0].push_back(i);  // degree[x][0]纪录x为正的个数
			    else LC[-x][1].push_back(i); // degree[x][1]纪录x为负的个数
		}
	LX.clear();
	for (int x=1;x<=n0;x++)
		if (TP[x]==-1 && (LC[x][0].size()==1 || LC[x][1].size()==1))
			LX.push_back(x);
	if (DM<=n*4) D3=true; //调节阀值
	        else D3=false;  

	D3=true;
}
vector<int> LC[NB_V][2];
vector<int> LX;
int degree[NB_V];
void branch(int &n,int &m,int n0,int m0,int *X,int &maxNum,int *ans,set<int> *C,set<int> *C0,int *TP,node* H,int Upbound){
	set<int>::iterator it;
    map<int,int > tTP;
    map<int,set<int> > tC;
    int tn=n,tm=m;
	bool D3; 
	tTP.clear();
	tC.clear();
	COUNT[0]++; 
	while (1){
		clock_t start;
		start=clock();
	//	puts("进入reNew");
		reNew(m,X,TP,H,C,Upbound,tC); //done
		TIME[0]+=clock()-start;
		if (Upbound<=maxNum){
			back(TP,C,n,m,tTP,tC,tn,tm); //还原现场
			return;
		}
		start=clock();
	//	puts("进入rule1_2");
		if (rule1_2(n,m,X,TP,H,C,Upbound,tC)) { TIME[10]+=clock()-start; COUNT[4]++; continue; } //done
		TIME[10]+=clock()-start; 
		start=clock();
	//	puts("进入rule2");
		if (rule2(n,m,X,TP,H,C,tTP)) { TIME[2]+=clock()-start; COUNT[2]++; continue; } //done
		TIME[2]+=clock()-start; 
		start=clock();
		getLC(n,m,C,LC,TP,D3,LX);
	//	puts("进入rule3");
		if (rule3(n,m,X,TP,H,C,LC,tTP,tC)) { TIME[3]+=clock()-start; COUNT[3]++; continue; } //done
		TIME[3]+=clock()-start; 
		if (D3){ //阀值
			start=clock(); 
	//		puts("进入rule6-7");
			rule6(n,m,TP,H,C,X,LC,tC,LX); //done
			TIME[6]+=clock()-start; 
			start=clock(); 
	//		puts("进入rule6-7");
			if (rule7(n,m,TP,H,C,X,LC,tC,tTP,LX))   { TIME[7]+=clock()-start; COUNT[7]++; continue; } //done
			TIME[7]+=clock()-start;  
		} 
		start=clock();
	//	puts("进入rule8");
		if (rule8(m,TP,C,Upbound,tC)) { TIME[8]+=clock()-start; COUNT[8]++; continue; } //done
		TIME[8]+=clock()-start;   
		break;
	} 
	reUB(n,m,C,Upbound);
	if (Upbound<=maxNum){
		back(TP,C,n,m,tTP,tC,tn,tm); //还原现场
		return; 
	}
	int k=0;
	memset(degree,0,sizeof(degree));
   	for (int i=1;i<=m;i++)
    	for (it=C[i].begin();it!=C[i].end();it++)
			degree[abs(*it)]++;	 
	for (int i=1;i<=n;i++){
		if (TP[i]!=-1) continue; 
		if (degree[k]<degree[i]) k=i; 
	}  
	if (k){ 
		if (tTP.find(k)==tTP.end())
			tTP[k]=TP[k]; //---纪录变化
		TP[k]=0; //值确定
		X[k]=0;
		branch(n,m,n0,m0,X,maxNum,ans,C,C0,TP,H,Upbound); 
		X[k]=1;
		branch(n,m,n0,m0,X,maxNum,ans,C,C0,TP,H,Upbound); 
		back(TP,C,n,m,tTP,tC,tn,tm); //还原现场 
		return;
	}
	consH(n0,TP,H,X,tTP); //展开递推关系TP,H
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
	back(TP,C,n,m,tTP,tC,tn,tm); //还原现场
	return;
}
set<int> C[NB_C],C0[NB_C];
int ans[NB_V],X[NB_V];
int TP[NB_V]; //TP存变量的状态是 -1 未知  0 为确定值  1 由H[i].F得到  2看H[i].fx之后得到
node H[NB_V];
int main(int argc,char **arg){
    freopen(arg[1],"r",stdin);
    int n,m,n0,maxNum=0;
    clock_t start,finish; 
    start=clock();
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
	finish=clock()-start;
	double sum=0;
	for (int i=0;i<=10;i++) sum+=TIME[i];
	printf("Total time is %.5lf seconds.\n",(double)finish/CLOCKS_PER_SEC);
	printf("reNew    : %.5lf seconds.   (%.2lf %%) \n",(double)TIME[0]/CLOCKS_PER_SEC,100.0*TIME[0]/finish); 
	printf("Rule 1.2 : %.5lf seconds.   (%.2lf %%) \n",(double)TIME[10]/CLOCKS_PER_SEC,100.0*TIME[10]/finish);
	for (int i=2;i<=8;i++){
		if (i==4 || i==5) continue;
		printf("Rule %d   : %.5lf seconds.   (%.2lf %%) \n",i,(double)TIME[i]/CLOCKS_PER_SEC,100.0*TIME[i]/finish);
	}
	printf("(%.2lf %%) \n\n",100.0*sum/finish);
	Output(maxNum);  
    return 0;
}
