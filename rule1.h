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
	for (int i=1;i<=n;i++){
		if (H[i].fx!=-1) continue;
		int p1,p2;
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