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
bool isNum(char c){
	if (c>='0' && c<='9') return true;
	if (c=='-') return true;
	return false;
} 
void initial(int &n,int &m,int *ans,set<int> *C){ //读取数据
	char s[1005];
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