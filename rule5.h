bool rule5(int n,int &m,int *X,set<int> *C){
	int p[3];
	for (int x=1;x<=n;x++){
		if (X[x]!=-1) continue; 
		for (int y=1;y<=n;y++){
			if (X[y]!=-1) continue;
			int count=0;
			for (int i=1;i<=m;i++){
				if (!find(C[i],x) && !find(C[i],-x)) continue;
				if (!find(C[i],y) && !find(C[i],-y)) break;
				p[count++]=i;
			}
			if (count!=3) continue;
			X[x]=X[y]=0;
			for (int i=0;i<3;i++) C[p[i]]=C[m--];
			return true;
		}
	}
	return false;
}