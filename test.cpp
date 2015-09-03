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
const int MAXN=100005;
set<int> C[MAXN];
set<int>::iterator it;
char s[MAXN];
int ans[MAXN],maxNum;
bool isNum(char c){
	if (c>='0' && c<='9') return true;
	if (c=='-') return true;
	return false;
}
bool find(int p,int x){
	return C[p].find(x)!=C[p].end();
}
bool n1n2MaxSAT(int n,int &m){
	for (int x=1;x<=n;x++){
		if (ans[x]!=-1) continue;
		int p[3];
		p[0]=p[1]=p[2]=0;
		for (p[0]=1;p[0]<=m;p[0]++)
			if (find(p[0],x) || find(p[0],-x)) break;
		for (p[1]=p[0]+1;p[1]<=m;p[1]++)
			if (find(p[1],x) || find(p[1],-x)) break;
		for (p[2]=p[1]+1;p[2]<=m;p[2]++)
			if (find(p[2],x) || find(p[2],-x)) break;
		if (p[0]>m){
			ans[x]=1;
			return true;
		}
		if (p[1]>m){ //----处理只出现在一个F的
			if (find(p[0],x)){
				ans[x]=1;
				C[p[0]].erase(x);
			}else{
				ans[x]=0;
				C[p[0]].erase(-x);
			}
			return true;
		}
		if (p[2]>m){  //----处理只出现在两个F的
			if (find(p[0],x) && find(p[1],x)){
				ans[x]=1;
				C[p[0]].erase(x),C[p[1]].erase(x);
				return true;
			}
			if (find(p[0],-x) && find(p[1],-x)){
				ans[x]=0;
				C[p[0]].erase(-x),C[p[1]].erase(-x);
				return true;			
			}
			ans[x]=1;
			for (it=C[p[1]].begin();it!=C[p[1]].end();it++)
				C[p[0]].insert(*it);
			C[p[0]].erase(-x),C[p[0]].erase(x);
			swap(C[p[1]],C[p[m--]]); 
			return true;
		}
		//----处理出现在三个F且都相同的
		if (find(p[0],x) && find(p[1],x) && find(p[2],x)){
			ans[x]=1;
			C[p[0]].erase(x),C[p[1]].erase(x),C[p[2]].erase(x);
			return true;
		}
		if (find(p[0],-x) && find(p[1],-x) && find(p[2],-x)){
			ans[x]=0;
			C[p[0]].erase(-x),C[p[1]].erase(-x),C[p[2]].erase(-x);
			return true;
		}
	}
	return false;
} 
bool singletons(int x,int m){
	for (int i=1;i<=m;i++)
		if (find(i,x) && C[i].size()==1) return true;
	return false;
}
void n3MaxSAT(int n,int m){
	while (n1n2MaxSAT(n,m));  
	int temp=0;
	for (int i=1;i<=n;i++)
		if (singletons(i,m)) temp++; 

}
int main(){
    freopen("input.txt","r",stdin);
    freopen("output.txt","w",stdout);
    int n,m;
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
    memset(ans,-1,sizeof(ans));
    maxNum=0;
    n3MaxSAT(n,m);
    printf("%d\n",maxNum);
    for (int i=1;i<=n;i++) printf("%d ",ans[i]);
    puts(""); 
    return 0;
}
