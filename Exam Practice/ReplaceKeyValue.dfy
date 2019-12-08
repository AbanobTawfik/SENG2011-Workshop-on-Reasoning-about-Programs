method Replace(arr: array<int>, oldVal: int, newVal: int)
requires arr != null
modifies arr
ensures forall i :: 0 <= i < arr.Length ==> if (old(arr[i]) == oldVal) then (arr[i] == newVal)
                                                                       else (arr[i] == old(arr[i]))
{
    var count := 0;
    
    while count < arr.Length
    invariant 0 <= count <= arr.Length
    invariant forall i :: count <= i < arr.Length ==> old(arr[i]) == arr[i] 
    invariant forall i :: 0 <= i < count ==> if (old(arr[i]) == oldVal) then (arr[i] == newVal)
                                                                        else (arr[i] == old(arr[i]))
    {
        if(arr[count] == oldVal)
        {
            arr[count] := newVal;
        }
        count := count + 1;
    }
}
