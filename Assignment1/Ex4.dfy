/////////////////////////////////////////////////////////////
//          ALL CODE IN HERE IS WRITTEN BY                 //
//                 ABANOB TAWFIK                           //
//                    Z5075490                             //
//                 September 2019                          //
/////////////////////////////////////////////////////////////

// Ex4.dfy 8 marks. 

// Write a Dafny method, called IncDec, that computes the sum of two integers
//  x and y by using increments (+1) and decrements (-1) only. 

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
    var increments;
    // return absolute value of y for loop bound
    var numberOfLoops;
    
    if y >= 0
    {
        numberOfLoops := y;
        increments := 1;
    }else{
        numberOfLoops := -1 * y;
        increments := -1;
    }
    
    while counter < numberOfLoops
    invariant counter <= numberOfLoops 
    invariant sum == x + (counter*increments);
    {
        sum := sum + increments;
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