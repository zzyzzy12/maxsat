bool rule2(int n,int &m,int *X,node *H,set<int> *C){ 
	for (int z=1;z<=n;z++){
		if (H[z].fx!=-1) continue;
		int i,j,t;
		i=j=t=0;
		for (int k=1;k<=m;k++){
			if (find(C[k],z)){
				i++;
				if (C[k].size()==1) t++;
			} 
			if (find(C[k],-z)) j++;
		}
		if (t<j) continue; 
		X[z]=1;
		H[z].fx=0; //z值确定
		return true;
	} 
	return false;
}