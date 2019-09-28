/////////////////////////////////////////////////////////////
//          ALL CODE IN HERE IS WRITTEN BY                 //
//         	       ABANOB TAWFIK						   //
//          		  Z5075490 			                   //
//				   September 2019						   //
/////////////////////////////////////////////////////////////

// Ex5.dfy 6 marks.
// An array is even-odd sorted if the array consists of
// even-sorted and odd-sorted sub-arrays.
// An even-sorted sub-array is an array in which
// all the values at even indexes are sorted. Analogously
// for an odd-sorted sub-array.

// An example is:
// [2,1,4,2,6,3]
// In this array, the even-sorted sub-array is [2,4,6],
// the odd-sorted sub-array is [1,2,3]
// The arrays [1,2], [2,1] and [] are even-odd sorted.
// The array [1,2,3,1] is not even-odd sorted.
// Write a Dafny predicate called EOSorted that, given an array,
// is true if the array is even-odd sorted, and
// false otherwise. Test the predicate behaves correctly
// by writing a method Test that calls the predicate
// for all the testcases mentioned above.

predicate EOSorted(a: array<int>)
requires a !=  null
reads a
// if all even + odd pairs are sorted return true post conidtion
ensures forall i,j :: 0 <= i <= j < a.Length - 2 && j == i+2 && (a[i] < a[j]) 
==> true ==> exists i,j :: 0 <= i <= j < a.Length - 2 && j == i+2 && (a[i] > a[j]) ==> false;
// doesn't modify array post condition
{
    forall i,j :: 0 <= i <= j < a.Length - 2 && j == i+2 ==> a[i] < a[j] 
    ==> !exists i,j :: 0 <= i <= j < a.Length - 2 && j == i+2 && (a[i] > a[j])
    
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

    assert EOSorted(testArray1);
    //assert test1 == false;

    assert EOSorted(testArray2);
    //assert test2 == true;

    assert EOSorted(testArray3);
    //assert test3 == true;

    assert EOSorted(testArray4);
    //assert test4 == true;

    assert EOSorted(testArray5);
    //assert test5 == false;

    //print test1, "--", test2, "--", test3, "--",test4, "--",test5, "--\n";
}