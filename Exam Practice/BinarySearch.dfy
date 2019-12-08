method BinarySearch(arr: array<int>, key: int) returns (index: int)
requires arr != null
requires Sorted(arr)
ensures -1 <= index < arr.Length
ensures (index == -1) ==> forall i :: 0 <= i < arr.Length ==> (arr[i] != key)
ensures (index >= 0) ==>  index < arr.Length && arr[index] == key && key in arr[..]
{
    var low := 0;
    var high := arr.Length;
    while(low < high)
    invariant 0 <= low <= high <= arr.Length
    invariant forall i :: 0 <= i < arr.Length && !(low <= i < high) ==> (arr[i] != key)
    {
        var mid := (high + low)/ 2;
        if(arr[mid]  > key)
        {
            high := mid;
        }
        else if(arr[mid] < key)
        {
            low := mid + 1;
        }
        else
        {
            return mid;
        }
    }
    return -1;
}

predicate Sorted(arr: array<int>)
reads arr
requires arr != null
{
    forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
}

method Main()
{
    var i;

    var a := new int[6];
    a[0], a[1], a[2], a[3], a[4], a[5] := 1, 3, 4, 6, 7, 8;
    assert a[..] == [1, 3, 4, 6, 7, 8];

    i := BinarySearch(a, 0);
    assert i == -1;
    i := BinarySearch(a, 1);
    assert a[0] == 1;
    assert i ==  0;
    i := BinarySearch(a, 2);
    assert i == -1;
    i := BinarySearch(a, 3);
    assert a[1] == 3;
    assert i ==  1;
    i := BinarySearch(a, 4);
    assert a[2] == 4;
    assert i ==  2;
    i := BinarySearch(a, 5);
    assert i == -1;
    i := BinarySearch(a, 6);
    assert a[3] == 6;
    assert i ==  3;
    i := BinarySearch(a, 7);
    assert a[4] == 7;
    assert i ==  4;
    i := BinarySearch(a, 8);
    assert a[5] == 8;
    assert i ==  5;
    i := BinarySearch(a, 9);
    assert i == -1;

    var b := new int[1];
    b[0] := 5;
    assert b[..] == [5];
    i := BinarySearch(b, 1);
    assert i == -1;
    i := BinarySearch(b, 5);
    assert b[0] == 5;
    assert i ==  0;
    i := BinarySearch(b, 9);
    assert i == -1;

    var c := new int[0];
    assert c[..] == [];
    i := BinarySearch(c, 5);
    assert i == -1;
}
