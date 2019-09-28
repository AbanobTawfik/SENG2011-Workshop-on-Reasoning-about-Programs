/////////////////////////////////////////////////////////////
//          ALL CODE IN HERE IS WRITTEN BY                 //
//         	       ABANOB TAWFIK						   //
//          		  Z5075490 			                   //
//				   September 2019						   //
/////////////////////////////////////////////////////////////

// Ex2.dfy 1 mark. 

// Verify in Dafny that every integer is either even or odd.

method main(number:int){
	var parity := number%2;
    assert parity == 0 || parity == 1;
}