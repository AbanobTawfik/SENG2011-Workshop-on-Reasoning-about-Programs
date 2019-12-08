method Reverse(arr: array<int>)
requires arr != null
modifies arr
ensures multiset(arr[..]) == multiset(old(arr[..]))
ensures forall i :: 0 <= i < arr.Length/2 ==> arr[i] == old(arr[arr.Length - 1 - i])
ensures forall i :: 0 <= i < arr.Length/2 ==> arr[arr.Length - 1 - i] == old(arr[i])
{
    var count := 0;
    while count < arr.Length / 2
    invariant 0 <= count <= arr.Length / 2
    invariant multiset(arr[..]) == multiset(old(arr[..]))
    invariant forall i :: count <= i <= arr.Length - 1 - count ==> arr[i] == old(arr[i])
    invariant forall i :: 0 <= i < count ==> arr[i] == old(arr[arr.Length - 1 - i])
    invariant forall i :: 0 <= i < count ==> arr[arr.Length - 1 - i] == old(arr[i])
    {
        arr[count], arr[arr.Length - 1 - count] := arr[arr.Length - 1 - count], arr[count];
        count := count + 1;
    }
}

method Reverse2(arr: array<int>)
requires arr != null
modifies arr
// ensures multiset(arr[..]) == multiset(old(arr[..]))
ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[arr.Length - 1 - i])
{
    forall i | 0 <= i < arr.Length     
    {
        arr[i] := arr[arr.Length - 1 - i]; 
    }
    // assert multiset(arr[..]) == multiset(old(arr[..]));
}
