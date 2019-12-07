method Just1(a: array<int>, key: int) returns (b: bool)
requires a != null
ensures b == (CountOccurences(a[0..a.Length], key) == 1)
ensures multiset(a[..]) == multiset(old(a[..]))
{
    var count := 0;
    var keyCount := 0;
    while count < a.Length
    invariant 0 <= count <= a.Length
    invariant keyCount == (CountOccurences(a[0..count], key))
    invariant multiset(a[..]) == multiset(old(a[..]))
    {
        if(a[count] == key)
        {
            keyCount := keyCount + 1;
        }
        count := count + 1;
    }
    
    b := (keyCount == 1);
}

function CountOccurences(a: seq<int>, key: int): int
ensures CountOccurences(a, key) == multiset(a)[key]
{
    multiset(a)[key]
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

    assert testArray2.Length == 1;
    assert testArray2[0] == 1;

    assert testArray3.Length == 0;

    assert testArray1[0..testArray1.Length] == [1, 1, 2, 1];
    var test1 := Just1(testArray1, 1);
    assert CountOccurences(testArray1[0..testArray1.Length], 1) == 3;
    assert !test1;


    var test2 := Just1(testArray1, 2);
    assert CountOccurences(testArray1[0..testArray1.Length], 2) == 1;
    assert test2;
    
    var test3 := Just1(testArray1, 3);
    assert CountOccurences(testArray1[0..testArray1.Length], 3) == 0;
    assert !test3;

    assert testArray2[0..testArray2.Length] == [1];
    var test4 := Just1(testArray2, 1);
    assert CountOccurences(testArray2[0..testArray2.Length], 1) == 1;
    assert test4;

    var test5 := Just1(testArray2, 2);
    assert CountOccurences(testArray2[0..testArray2.Length], 2) == 0;
    assert !test5;

    assert testArray3[0..testArray3.Length] == []; 
    var test6 := Just1(testArray3, 1);
    assert CountOccurences(testArray3[0..testArray3.Length], 1) == 0;
    assert !test6;

    print test1, "\n", test2, "\n", test3, "\n", test4, "\n", test5, "\n", test6, "\n";
}
