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