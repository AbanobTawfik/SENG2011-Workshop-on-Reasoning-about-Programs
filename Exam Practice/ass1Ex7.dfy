method Just1(a: array<int>, key: int) returns (b: bool)
requires a != null
ensures b == (CountOccurences(a, key, a.Length - 1) == 1)
{
    var count := 0;
    var keyCount := 0;
    while count < a.Length
    invariant 0 <= count <= a.Length
    invariant keyCount == (CountOccurences(a, key, count - 1))
    {
        if(a[count] == key)
        {
            keyCount := keyCount + 1;
        }
        count := count + 1;
    }
    
    b := (keyCount == 1);
}

function CountOccurences(a: array<int>, key: int, high: int): int
reads a
decreases high
requires a != null
requires high < a.Length
ensures (high >= 0 && a[high] == key) ==> (CountOccurences(a, key, high) == 1 + CountOccurences(a, key, high - 1))
ensures (high >= 0 && a[high] != key) ==> (CountOccurences(a, key, high) == CountOccurences(a, key, high - 1))  
{
    if high >= 0
    then
        if a[high] == key
        then
            1 + CountOccurences(a, key, high - 1)
        else
            CountOccurences(a, key, high - 1)
    else 
        0    
}

predicate VerifyJustOne(a: array<int>, key: int)
reads a
requires a != null
{
    (forall i, j :: 0 <= i <= j < a.Length && (a[i] == key) && (a[i] == a[j]) ==> (i == j)) &&
    (exists i :: 0 <= i < a.Length && a[i] == key) 
}

method Main()
{
    var testArray1: array<int> := new int[4];
    testArray1[0], testArray1[1], testArray1[2],testArray1[3] := 1, 1, 2, 1;
    var testArray2: array<int> := new int[1];
    testArray2[0] := 1;
    var testArray3: array<int> := new int[0];

    assert testArray1.Length == 4;
    assert testArray1[0] == 1;
    assert testArray1[1] == 1;
    assert testArray1[2] == 2;
    assert testArray1[3] == 1;
    var test1 := Just1(testArray1, 1);
    assert (CountOccurences(testArray1, 1, testArray1.Length - 1) == 3);
    assert !VerifyJustOne(testArray1, 1);
    assert !test1;

    assert testArray1.Length == 4;
    assert testArray1[0] == 1;
    assert testArray1[1] == 1;
    assert testArray1[2] == 2;
    assert testArray1[3] == 1;
    var test2 := Just1(testArray1, 2);
    assert (CountOccurences(testArray1, 2, testArray1.Length - 1) == 1);
    assert VerifyJustOne(testArray1, 2);
    assert test2;
    
    assert testArray1.Length == 4;
    assert testArray1[0] == 1;
    assert testArray1[1] == 1;
    assert testArray1[2] == 2;
    assert testArray1[3] == 1;
    var test3 := Just1(testArray1, 3);
    assert (CountOccurences(testArray1, 3, testArray1.Length - 1) == 0);
    assert !VerifyJustOne(testArray1, 3);
    assert !test3;

    assert testArray2.Length == 1;
    assert testArray2[0] == 1;
    var test4 := Just1(testArray2, 1);
    assert (CountOccurences(testArray2, 1, testArray2.Length - 1) == 1);
    assert VerifyJustOne(testArray2, 1);
    assert test4;

    assert testArray2.Length == 1;
    assert testArray2[0] == 1;
    var test5 := Just1(testArray2, 2);
    assert (CountOccurences(testArray2, 2, testArray2.Length - 1) == 0);
    assert !VerifyJustOne(testArray2, 2);
    assert !test5;

    assert testArray3.Length == 0;
    var test6 := Just1(testArray3, 1);
    assert (CountOccurences(testArray3, 1, testArray3.Length - 1) == 0);
    assert !VerifyJustOne(testArray3, 1);
    assert !test6;

    print test1, "\n", test2, "\n", test3, "\n", test4, "\n", test5, "\n", test6, "\n";
}


