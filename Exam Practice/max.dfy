method max(arr:array<int>) returns (val:int)
requires arr != null
ensures (arr.Length == 0) ==> (val == -1)
ensures (arr.Length > 0) ==> val in arr[..]
ensures forall i :: 0 <= i < arr.Length ==> val >= arr[i] 
{
    if(arr.Length == 0)
    {
        val := -1;
        return;
    }
    var i := 1;
    var max := arr[0];
    while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant max in arr[..i]
    invariant forall j :: 0 <= j < i ==> max >= arr[j]
    {
        if(arr[i] >= max)
        {
            max := arr[i];
        }
        i := i + 1;
    }
    val := max;
}

method Main()
{
    var test1 := new int[0];
    var x := max(test1);
    assert x == -1;
    print x;
    
    var test2 := new int[3];
    test2[0], test2[1], test2[2] := 1, 2, 2;
    var x2 := max(test2);
    assert test2[1] == 2;
    assert 2 == x2;
    print x2;
}
