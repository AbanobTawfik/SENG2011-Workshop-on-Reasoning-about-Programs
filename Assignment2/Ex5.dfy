predicate Sorted(a: array<int>, start: int, end: int)
requires a != null;
reads a
requires 0 <= start < end <= a.Length
{
    forall i, j :: start <= i < j < end ==> (a[i] < a[j])
}

method Main()
{  // SUBMIT THIS MAIN METHOD WITH YOUR CODE
   var a := new int[2];
   a[0]:=34; a[1]:=12;
   assert a[..]==[34,12];
   ghost var ms := multiset(a[..]);
   //Shuffle(a);
   //assert a[..]==[12,34];
   assert Sorted(a, 0, a.Length);
   assert ms == multiset(a[..]);
   print a[..];

   var b := new int[4];
   b[0]:=78; b[1]:=56; b[2]:=34; b[3]:=12;
   assert b[..]==[78,56,34,12];
   ms := multiset(b[..]);
   //Shuffle(b);
   //assert b[..]==[12,34,56,78];
   assert Sorted(a, 0, a.Length);
   assert ms == multiset(b[..]);
   print b[..], '\n';
}