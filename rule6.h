bool rule6(int &n,int &m,int *X,node *H,set<int> *C){ //把(~x,~y,C2)中的x去掉 x=(~y,C2) 
	for (int x=1;x<=n;x++){
		if (H[x].fx!=-1) continue;
		for (int y=1;y<=n;y++){
			if (H[y].fx!=-1) continue;
			int p1,p2;
			p1=p2=0;
			for (int i=1;i<=m;i++){
				if (find(C[i],x) && find(C[i],y)) p1=i;
				if (find(C[i],-x) && find(C[i],-x)) p2=i;
			}
			if (!p1 || !p2) continue;
			C[p1].erase(x);
			return true;
		}
	}
	return false;
}