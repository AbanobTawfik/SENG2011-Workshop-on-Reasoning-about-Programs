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
    assert testArray1[..] == [1, 1, 2, 1];
    assert multiset(testArray1[..]) == multiset{1, 1, 2, 1};
    //assert multiset(testArray1[..])[1] == 3;

}