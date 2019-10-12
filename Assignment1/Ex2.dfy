/////////////////////////////////////////////////////////////
//          ALL CODE IN HERE IS WRITTEN BY                 //
//                 ABANOB TAWFIK                           //
//                    Z5075490                             //
//                 September 2019                          //
/////////////////////////////////////////////////////////////

// Ex2.dfy 1 mark. 

// Verify in Dafny that every integer is either even or odd.

method main(number:int){
    // the parity of a number is it's remainder when divided by 2
    // parity == 1 means the number is odd
    // parity == 0 means the number is even
    var parity := number%2;
    // the assert states that the parity is either 0 or 1, verifying the statement
    assert parity == 0 || parity == 1;
}