bool rule7(int &n,int &m,int *X,node *H,set<int> *C){
	int p[2][2];
	for (int x=1;x<=n;x++){
		if (H[x].fx!=-1) continue;
		int t1,t2;
		t1=t2=0;
		for (int i=1;i<=m;i++){
			if (find(C[i],x)) p[0][t1++]=i;
			if (find(C[i],-x)) p[1][t2++]=i;
		}
		if (t1!=2 || t2!=1) continue;
		for (int y=1;y<=n;y++){
			if (H[y].fx!=-1) continue;
			if (find(C[p[1][0]],y)) continue; //小改 交换了y -y
			if (find(C[p[0][0]],-y) && find(C[p[0][1]],y)){
				C[p[0][1]].erase(x);
				return true;
			}
			if (find(C[p[0][0]],y) && find(C[p[0][1]],-y)){
				C[p[0][0]].erase(x);
				return true;
			}
		}
	}
	return false;
}