bool rule3(int n,int &m,int *X,node *H,set<int> *C){
	set<int>::iterator it;
	for (int i=1;i<=n;i++){
		if (H[i].fx!=-1) continue;
		int p[3];
		p[0]=p[1]=p[2]=0;
		for (p[0]=1;p[0]<=m;p[0]++)
			if (find(C[p[0]],i) || find(C[p[0]],-i)) break;
		for (p[1]=p[0]+1;p[1]<=m;p[1]++)
			if (find(C[p[1]],i) || find(C[p[1]],-i)) break;
		for (p[2]=p[1]+1;p[2]<=m;p[2]++)
			if (find(C[p[2]],i) || find(C[p[2]],-i)) break;
		if (p[0]>m){ //clause中无i,任意赋值
			X[i]=0;
			H[i].fx=0; //值为0/1
			return true;
		}
		if (p[1]>m){ //----处理只出现在一个F的
			if (find(C[p[0]],i)) X[i]=1;
						   else  X[i]=0;  
			H[i].fx=0; //值为0/1 不用看H[i].F
			return true;
		}
		if (p[2]>m){  //----处理只出现在两个F的
			if (find(C[p[0]],i) && find(C[p[1]],i)){
				X[i]=1;
				H[i].fx=0;
				return true;
			} 
			if (find(C[p[1]],i)) swap(p[0],p[1]);

			H[i].fx=1,H[i].F=C[p[1]]; //值由H[i].F决定，而不看H[i].fx


			for (it=C[p[1]].begin();it!=C[p[1]].end();it++)
				C[p[0]].insert(*it);
			C[p[0]].erase(-i),C[p[0]].erase(i);
			C[p[1]]=C[p[m--]];
			return true;
		}
		//----处理出现在三个F且都相同的
		if (find(C[p[0]],i) && find(C[p[1]],i) && find(C[p[2]],i)){
			X[i]=1;  
			H[i].fx=0;
			return true;
		}
	}
	return false;
}