predicate EOSorted(arr: array<int>)
reads arr
requires arr != null
{
    forall i, j :: 0 <= i < arr.Length - 2 && (j == i + 2) ==> arr[i] <= arr[j] &&
    !exists i, j :: 0 <= i < arr.Length - 2 && (j == i + 2) && arr[i] > arr[j]
}

method Test()
{
    var testArray1: array<int> := new int[6];
    testArray1[0], testArray1[1], testArray1[2],testArray1[3],testArray1[4], testArray1[5] := 2, 1, 4, 2, 6, 3;

    var testArray2: array<int> := new int[2];
    testArray2[0], testArray2[1] := 1, 2;

    var testArray3: array<int> := new int[2];
    testArray3[0], testArray3[1] := 2, 1;

    var testArray4: array<int> := new int[0];

    var testArray5: array<int> := new int[4];
    testArray5[0], testArray5[1], testArray5[2],testArray5[3] := 1, 2, 3, 1;

    assert testArray1.Length == 6;
    assert testArray1[0] == 2;
    assert testArray1[1] == 1;
    assert testArray1[2] == 4;
    assert testArray1[3] == 2;
    assert testArray1[4] == 6;
    assert testArray1[5] == 3;
    assert EOSorted(testArray1);

    assert testArray2.Length == 2;
    assert testArray2[0] == 1;
    assert testArray2[1] == 2;
    assert EOSorted(testArray2);

    assert testArray3.Length == 2;
    assert testArray3[0] == 2;
    assert testArray3[1] == 1;
    assert EOSorted(testArray3);

    assert testArray4.Length == 0;
    assert EOSorted(testArray4);

    assert testArray5.Length == 4;
    assert testArray5[0]  == 1;
    assert testArray5[1] == 2;
    assert testArray5[2] == 3;
    assert testArray5[3] == 1;
    assert !EOSorted(testArray5);
}
