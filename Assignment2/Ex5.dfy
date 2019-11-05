predicate Sorted(a: array<int>, start: int, end: int)
requires a != null;
reads a
requires 0 <= start <= end <= a.Length
{
    forall i, j :: start <= i < j < end ==> (a[i] <= a[j])
}

method Shuffle(arr: array<int>)
requires arr != null
modifies arr
ensures multiset(arr[..]) == multiset(old(arr[..]))
ensures Sorted(arr, 0, arr.Length)
{
    // array of length 0 is already sorted
    if(arr.Length >= 1){
        var up := 1;
        while up < arr.Length
        invariant 1 <= up <= arr.Length
        invariant Sorted(arr, 0, up)
        invariant multiset(arr[..]) == multiset(old(arr[..]))
        {
            // i call this variable sifted down index since we are essentially 
            // sifting down to the correct position to insert it
            var siftedDownIndex := up;
            // put this here since we will be CORRUPTING OUR MULTISET WE WANT TO REMEMBER WHAT WE ARE SHIFTING DOWN
            // we want to remember the value we corrupt out to reintroduce it back in after the loop is complete
            // and we have found the right position to reintroduce it
            var rogue := arr[siftedDownIndex];
            while (siftedDownIndex > 0) && (arr[siftedDownIndex - 1] > rogue)
            invariant 1 <= up <= arr.Length
            invariant 0 <= siftedDownIndex <= up
            invariant forall i :: siftedDownIndex <= i <= up ==> arr[i] >= rogue 
            // on every iteration, everything from 0 to the up index in the outer loop
            // will be sorted, except for the rogue value (hence the j != shiftedDownIndex)
            // this is almost identical to the example in the lecture, however the difference is that
            // the lower section before our rogue value is always sorted
            // the blow invariant will hold on up even though its rogue, because the shifted down index is initally up
            // and as we 
            invariant forall i, j :: 0 <= i < j <= up && j != siftedDownIndex ==> arr[i] <= arr[j]
            invariant Sorted(arr, 0, siftedDownIndex)
            invariant Sorted(arr, 0, up)
            invariant arr[siftedDownIndex] >= rogue
            // our current multiset will be the old array
            // and take away the rogue since it will be overwritten from the first call
            // then we add the element we overrwrite with. 
            // after the loop is finished our rogue will be placed back at the sifted down index
            // restoring our initial multiset!!
            invariant multiset(arr[..]) == multiset(old(arr[..])) - multiset{rogue} + multiset{arr[siftedDownIndex]}
            {
                // shuffle down BUT WE ARE BREAKING THE MULTISET HERE SINCE THE VERY FIRST VALUE WILL BE OVERWRITTEN
                arr[siftedDownIndex] := arr[siftedDownIndex - 1];
                siftedDownIndex := siftedDownIndex - 1;
            }
            // here is where we restore our multiset from corruption
            // we will uncorrupt our array, and reinsert the rogue value we initally overrode in it's correctly ordered position
            // we have sifted down to the right spot to put the rogue value to make it no longer rogue
            arr[siftedDownIndex] := rogue;
            up := up + 1;

        }
    }
}

method Main()
{  // SUBMIT THIS MAIN METHOD WITH YOUR CODE
   var a := new int[2];
   a[0]:=34; a[1]:=12;
   assert a[..]==[34,12];
   ghost var ms := multiset(a[..]);
   Shuffle(a);
   assert a[..]==[12,34];
   assert Sorted(a, 0, a.Length);
   assert ms == multiset(a[..]);
   print a[..];

   var b := new int[4];
   b[0]:=78; b[1]:=56; b[2]:=34; b[3]:=12;
   assert b[..]==[78,56,34,12];
   ms := multiset(b[..]);
   Shuffle(b);
   assert b[..]==[12,34,56,78];
   assert Sorted(a, 0, a.Length);
   assert ms == multiset(b[..]);
   print b[..], '\n';
}