/////////////////////////////////////////////////////////////
//          ALL CODE IN HERE IS WRITTEN BY                 //
//                 ABANOB TAWFIK                           //
//                    Z5075490                             //
//                 September 2019                          //
/////////////////////////////////////////////////////////////

// Ex4.dfy 8 marks. 

// Write a Dafny method, called IncDec, that computes the sum of two integers
//  x and y by using increment (+1) and decrements (-1) only. 

// Verify the method is correct.
// So, for example:

// 2 + 4 = 2 +1+1+1+1 = 6
// 19 + (-3) = 19 -1-1-1 = 16
// (-5) + (-3) = -5 -1-1-1 = -8
// 1

// Your method should use iteration, and only a single loop, 
// Include a method Test that verifies that IncDec behaves 
// correctly for the testcases:

// • 5 and 15
// • 5 and -15
// • 5 and 0
// • -5 and 15
// • -5 and -15
// • -5 and 0

// No output need be generated.
method IncDec(x: int, y: int) returns (sum: int)
ensures sum == x + y
{
    sum := x;
    var counter := 0;
    // variable either +1 or -1 based on if y >= 0, will increment and decrement
    // with this vairable
    var increment;
    // we want to do this all in 1 loop, in order to do this we need to first 
    // check if the value is being incremented on decremented
    // if y is non-negative, we want to increment, so we just leave the loop
    // to its natural addition 
    // if y is negative, we want to flip the increment and the bound
    // meaning we will be adding -1, which is the same as decrementing 
    var iterations;    
    if y >= 0
    {
        iterations := y;
        increment := 1;
    }
    else
    {
        iterations := -1 * y;
        increment := -1;
    }
    // our value of increment will hold the sign of y
    // y > 0 ==> increment = 1
    // y < 0 ==> increment = -1
    // so by the end of the loop the value of y should be counter*increment
    while counter < iterations
    invariant counter <= iterations 
    invariant sum == x + (counter*increment);
    {
        sum := sum + increment;
        counter := counter + 1;
    }
}

method Test()
{
    var testValue1 := IncDec(5, 15);
    assert testValue1 == 20;

    var testValue2 := IncDec(5, -15);
    assert testValue2 == -10;

    var testValue3 := IncDec(5, 0);
    assert testValue3 == 5;

    var testValue4 := IncDec(-5, 15);
    assert testValue4 == 10;

    var testValue5 := IncDec(-5, -15);
    assert testValue5 == -20;

    var testValue6 := IncDec(-5, 0);
    assert testValue6 == -5;     
}