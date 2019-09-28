/////////////////////////////////////////////////////////////
//          ALL CODE IN HERE IS WRITTEN BY                 //
//         	       ABANOB TAWFIK						   //
//          		  Z5075490 			                   //
//				   September 2019						   //
/////////////////////////////////////////////////////////////

// Ex1.dfy 1 mark.

// Verify in Dafny that the following predicate is a tautology.
// (((p or q) implies r) and (r implies s)) implies (~s implies ~p)
// where p, q, r and s are Booleans, and the tilde is the negation operator.

method main(p:bool, q:bool, r:bool, s:bool){
	assert (((p || q) ==> r) && (r ==> s)) ==> (!s ==> !p);
}