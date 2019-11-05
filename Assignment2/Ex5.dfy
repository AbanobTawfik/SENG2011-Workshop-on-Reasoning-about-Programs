/////////////////////////////////////////////////////////////
//       ALL CODE IN HERE NOT IN MAIN IS WRITTEN BY        //
//                 ABANOB TAWFIK                           //
//                    Z5075490                             //
//                 November 2019                           //
/////////////////////////////////////////////////////////////

// Ex5.dfy 15 marks
// Write a verified method Shuffle(a: array<int>) that implements an insertion sort using a shufflebased strategy 
// (as against the swap-based insertion sort that was given in the Week 7 lecture).
// The sort should be carried out in place, which means that the array self is modified in the sort, and that
// no other array may be used. There is no return variable.
// A Main() method to test your insertion sort is provided on the website. The method, shown below,
// calls a predicate Sorted() to verify the array is sorted. This predicate can be found in lectures.

predicate Sorted(a: array<int>, start: int, end: int)
requires a != null;
reads a
requires 0 <= start <= end <= a.Length
{
    forall i, j :: start <= i < j < end ==> (a[i] <= a[j])
}

// this is an almost identical approach to the lecture where it swaps till its in the right place
// however what we do here instead is save the swap till the very end
// since the array will maintain order from 0 --> up, we can just find the exact spot to put the rogue element
// at up, and swap at the very end. the  tricky part is realising that in the inner loop we are actually
// corrupting our multiset by overwriting the element at our siftingDownIndex with the one behind it
// but we should also realise, we are removing the the rogue, and adding in the overwritten one at the sifted down index
// note however, when we finish the loop we then write into the final sifted down index (Correct spot for rogue element)
// the rogue element, meaning that the by the end, we are removing rogue element then addding it back in fixing the multiset
// temporary corruption. however something different then the example in the lecture is that everything from 0 --> up will
// ALWAYS be sorted, except for the elements pointing after up

// i wrote this code in c# and output the steps on an array, and here is the log from the very last step

// 3, 12, 34, 38, 49, 56, 58, 78, 9,   - shiftedDownIndex: 8
// 3, 12, 34, 38, 49, 56, 58, 78, 78,  - shiftedDownIndex: 7
// 3, 12, 34, 38, 49, 56, 58, 58, 78,  - shiftedDownIndex: 6
// 3, 12, 34, 38, 49, 56, 56, 58, 78,  - shiftedDownIndex: 5
// 3, 12, 34, 38, 49, 49, 56, 58, 78,  - shiftedDownIndex: 4
// 3, 12, 34, 38, 38, 49, 56, 58, 78,  - shiftedDownIndex: 3
// 3, 12, 34, 34, 38, 49, 56, 58, 78,  - shiftedDownIndex: 2
// 3, 12, 12, 34, 38, 49, 56, 58, 78,  - shiftedDownIndex: 1
// FOUND SPOT 3 < 9
// 3, 9, 12, 34, 38, 49, 56, 58, 78,   - shiftedDownIndex: 1

// as we can see initially eveyrthing up till the rogue value 9 is sorted
// but once we take away 9 and do the first override, everything is sorted, but there is a duplicate element
// in the invariant where i add j != shiftedDownIndex, it says that initially everything is sorted till the rogue element
// and once we remove the rogue element the shiftedDownIndex will contain the duplicate, so not  including will have no impact
// but maintain the fact that the array is sorted through all the way after we put the rogue value back in
// so the invariant is true BEFORE since we disinclude the rogue value, during since we just ignore the duplicate override
// and after when the rogue value is put in the right spot

// despite the file looking huge there is only 33 lines of actual code (the rest is explanation and annotations)
method Shuffle(arr: array<int>)
requires arr != null
modifies arr
ensures multiset(arr[..]) == multiset(old(arr[..]))
ensures Sorted(arr, 0, arr.Length)
{
    // array of length 0 and 1 is already sorted
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
            // on every iteration, everything from 0 to the up index in the outer loop
            // will be sorted, except for the rogue value (hence the j != shiftedDownIndex)
            // this is almost identical to the example in the lecture, however the difference is that
            // the lower section before our rogue value is always sorted
            // the below invariant will hold on up even though the elements are being overwritten
            // as orderding is always maintained. the in depth explanation for why j != shiftedDownIndex is above
            // before the code where i run through an example
            invariant forall i, j :: 0 <= i < j <= up && j != siftedDownIndex ==> (arr[i] <= arr[j])
            invariant Sorted(arr, 0, siftedDownIndex)
            invariant Sorted(arr, 0, up)
            // sifting down only occurs when the value at the index is larger than rogue
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