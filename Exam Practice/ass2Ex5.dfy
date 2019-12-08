method Shuffle(arr: array<int>)
requires arr != null
modifies arr
ensures multiset(arr[..]) == multiset(old(arr[..]))
ensures Sorted(arr)
{
    var count := 0;
    while count < arr.Length
    invariant 0 <= count <= arr.Length
    invariant forall i, j :: 0 <= i < j < count ==> arr[i] <= arr[j]
    invariant multiset(arr[..]) == multiset(old(arr[..]))
    {
        var curr := count;
        var rogue := arr[count];
        while (curr >= 1 && arr[curr - 1] > rogue)
        invariant 0 <= count <= arr.Length
        invariant 0 <= curr <= count
        invariant forall i, j :: 0 <= i < j <= count && j != curr ==> arr[i] <= arr[j]
        invariant arr[curr] >= rogue
        invariant multiset(arr[..]) == multiset(old(arr[..])) - multiset{rogue} + multiset{arr[curr]}
        {
            arr[curr] := arr[curr - 1];
            curr := curr - 1;
        }
        arr[curr] := rogue;
        count := count + 1;
    }
}

predicate Sorted(arr: array<int>)
reads arr
requires arr != null
{
    forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
}

method Main()
{  // SUBMIT THIS MAIN METHOD WITH YOUR CODE
   var a := new int[2];
   a[0]:=34; a[1]:=12;
   assert a[..]==[34,12];
   ghost var ms := multiset(a[..]);
   Shuffle(a);
   assert a[..]==[12,34];
   assert Sorted(a);
   assert ms == multiset(a[..]);
   print a[..];

   var b := new int[4];
   b[0]:=78; b[1]:=56; b[2]:=34; b[3]:=12;
   assert b[..]==[78,56,34,12];
   ms := multiset(b[..]);
   Shuffle(b);
   assert b[..]==[12,34,56,78];
   assert Sorted(b);
   assert ms == multiset(b[..]);
   print b[..], '\n';
}
