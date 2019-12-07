method BubbleSort(arr: array<int>)
modifies arr
requires arr != null
ensures Sorted(arr)
ensures multiset(arr[..]) == multiset(old(arr[..]))
{
    if(arr.Length == 0)
    {
        return;
    }
    else
    {
        var i := arr.Length - 1;
        while i > 0
        invariant 0 <= i <= arr.Length
        invariant SortedBetween(arr, i, arr.Length)
        invariant multiset(arr[..]) == multiset(old(arr[..]))
        invariant partitioned(arr, i)
        {
            var j := 0;
            while j < i
            invariant 0 <= j <= i
            invariant SortedBetween(arr, i, arr.Length)
            invariant partitioned(arr, i)
            invariant multiset(arr[..]) == multiset(old(arr[..]))
            invariant forall k :: 0 <= k <= j ==> arr[j] >= arr[k]
            {
                if(arr[j] > arr[j + 1])
                {
                    arr[j], arr[j + 1] := arr[j + 1], arr[j];
                }
                j := j + 1;
            }
            i := i - 1;
        }
    }
}

predicate partitioned(arr: array<int>, index: int)
reads arr
requires arr != null
{
    forall i, j :: 0 <= i <= index < j < arr.Length ==> (arr[j] >= arr[i])
}

predicate SortedBetween(arr: array<int>, low: int, high: int)
reads arr
requires arr != null
requires low >= 0 && high >= 0
requires low <= arr.Length && high <= arr.Length
{
    forall i, j :: low <= i < j < high ==> (arr[j] >= arr[i])
}

predicate Sorted(arr: array<int>)
reads arr
requires arr != null
{
    forall i, j :: 0 <= i < j < arr.Length ==> (arr[j] >= arr[i])
}

method Main()
{
    var test1 := new int[0];
    BubbleSort(test1);
    assert Sorted(test1);
    
    var test2 := new int[5];
    test2[0], test2[1], test2[2], test2[3], test2[4] := 1, 3, 0, 2, 69;
    assert test2[0] == 1;
    assert test2[1] == 3;
    assert test2[2] == 0;
    assert test2[3] == 2;
    assert test2[4] == 69;
    assert !Sorted(test2);
    BubbleSort(test2);
    assert Sorted(test2);
    print test2[0], " ", test2[1], " ", test2[2], " ", test2[3], " ", test2[4], "\n";
}
