Method main(p:bool, q:bool, r:bool, s:bool){
	assert (((p || q) ==> r) && (r ==> s)) ==> (!s ==> !p);
}