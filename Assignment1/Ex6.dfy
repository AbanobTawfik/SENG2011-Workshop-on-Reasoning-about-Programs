/////////////////////////////////////////////////////////////
//          ALL CODE IN HERE IS WRITTEN BY                 //
//                 ABANOB TAWFIK                           //
//                    Z5075490                             //
//                 September 2019                          //
/////////////////////////////////////////////////////////////

// Ex6.dfy 6 marks. 
// Write a Dafny method IsClean:
// The method returns true if and only if the array is clean: 
// that is, if there are no instances of the integer
// key in the array a. The array is considered unclean, hence clean is false, 
// if there are one or more instances of the key in the array.
// Write a test method Main that calls IsClean to verify whether the following arrays are clean of the
// given key:
// • array [1,2,2,2,3] for the key 1
// • array [1,2,2,2,3] for the key 2
// • array [1,2,2,2,3] for the key 3
// • array [1,2,2,2,3] for the key 4
// • array [1] for the key 1
// • array [1] for the key 2
// • the empty array for the key 1

// and prints the corresponding results:
// False
// False
// False
// True
// False
// True
// True

method IsClean(a: array<int>, key: int) returns (clean: bool)
requires a != null
ensures clean == VerifyCleanArray(a, key)
ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i])
{
    // assume the array is clean initially (invariant will hold)
    clean := true;
    var i := 0;
    while i < a.Length
    invariant 0 <= i <= a.Length
    // note below is the expanded version of the predicate 
    // up till the index of our current iteration
    invariant clean == forall j :: 0 <= j < i ==> a[j] != key
    {
        // if we find a instance of the key, we overwrite clean to be false
        // maintaining the invariant
        if(a[i] == key)
        {
            clean := false;
        }
        i := i + 1;
    }
    // note now the value of clean will be either our inital assumption of true
    // or it will be false if we encountered a counter example
    // return the value of clean
}

predicate VerifyCleanArray(a: array<int>, key: int)
requires a != null;
reads a;
{
    forall i :: 0 <= i < a.Length ==> (a[i] != key)
}

method Main()
{
    var testArray1: array<int> := new int[5];
    testArray1[0], testArray1[1], testArray1[2],testArray1[3],testArray1[4] := 1, 2, 2, 2, 3;

    var testArray2: array<int> := new int[1];
    testArray2[0] := 1;

    var testArray3: array<int> := new int[0];
    
    assert testArray1.Length == 5;
    assert testArray1[0] == 1;
    assert testArray1[1] == 2;
    assert testArray1[2] == 2;
    assert testArray1[3] == 2;
    assert testArray1[4] == 3;


    assert testArray3.Length == 0;

    var test1 := IsClean(testArray1, 1);
    assert !VerifyCleanArray(testArray1, 1);
    assert !test1;
    assert !VerifyCleanArray(testArray1, 1) && !test1;

    var test2 := IsClean(testArray1, 2);
    assert !VerifyCleanArray(testArray1, 2);
    assert !test2;
    assert !VerifyCleanArray(testArray1, 2) && !test2;

    var test3 := IsClean(testArray1, 3);
    assert !VerifyCleanArray(testArray1, 3);
    assert !test3;
    assert !VerifyCleanArray(testArray1, 3) && !test3;

    var test4 := IsClean(testArray1, 4);
    assert VerifyCleanArray(testArray1, 4);
    assert test4;
    assert VerifyCleanArray(testArray1, 4) && test4;

    assert testArray2.Length == 1;
    assert testArray2[0] == 1;
    
    var test5 := IsClean(testArray2, 1);
    assert !VerifyCleanArray(testArray2, 1);
    assert !test5;
    assert !VerifyCleanArray(testArray2, 1) && !test5;
    
    var test6 := IsClean(testArray2, 2);
    assert VerifyCleanArray(testArray2, 2);
    assert test6;
    assert VerifyCleanArray(testArray2, 2) && test6;

    var test7 := IsClean(testArray3, 1);
    assert VerifyCleanArray(testArray3, 1);
    assert test7;
    assert VerifyCleanArray(testArray3, 1) && test7;

    print test1, "\n", test2, "\n", test3, "\n", test4, "\n", test5, "\n", test6, "\n", test7, "\n";
}
