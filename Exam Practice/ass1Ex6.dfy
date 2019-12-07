method IsClean(a: array<int>, key: int) returns (clean: bool)
requires a != null
ensures clean == VerifyCleanArray(a, key)
ensures multiset(a[..]) == multiset(old(a[..]))
{
    clean := true;
    var count := 0;
    while count < a.Length
    invariant 0 <= count <= a.Length
    invariant clean == forall i :: 0 <= i < count ==> a[i] != key
    invariant multiset(a[..]) == multiset(old(a[..]))
    {
        if(a[count] == key)
        {
            clean := false;
        }
        count := count + 1;
    }   
}

predicate VerifyCleanArray(a: array<int>, key: int)
reads a
requires a != null
{
    forall i :: 0 <= i < a.Length ==> a[i] != key && 
    !exists i :: 0 <= i < a.Length && a[i] == key
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
