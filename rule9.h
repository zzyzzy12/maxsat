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