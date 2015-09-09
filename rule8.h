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