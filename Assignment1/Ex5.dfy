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

method EOSorted(a: array<int>) returns(IsEoSorted:bool)
requires a !=  null
// ensures ___ ==> true
ensures a.Length >= 0 && a.Length <= 2 ==> true
// if all even + odd pairs are sorted return true post conidtion 
ensures forall i,j :: 0 <= i <= j < a.Length - 2 && j == i+2 && (a[i] < a[j]) ==> true 
// if a pair of even/odd are not sorted, return false post condition
//ensures exists i,j :: 0 <= i <= j < a.Length - 2 && a.Length > 2  && j == i+2  && (a[i] > a[j]) ==> false;
// doesn't modify array post condition
ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) 
{
    if(a.Length > 2){
        var i := 0;
        IsEoSorted := false;
        while i < a.Length - 2
        invariant 0 <= i <= a.Length - 2
        //invariant exists i,j :: 0 <= i <= j < a.Length - 2 && a.Length > 2  && j == i+2  && (a[i] > a[j]) ==> (IsEoSorted == false)
        {
            if(a[i] > a[i+2]){
                IsEoSorted := false;
                return;
            }
            i := i + 1;
        }
        IsEoSorted := true;
    }else{
        IsEoSorted := true;
    }
    // if(exists i,j :: 0 <= i <= j < a.Length - 2 && a.Length > 2  && j == i+2  && (a[i] > a[j])){
    //     IsEoSorted := false;
    // }else{
    //     IsEoSorted := true;
    // }
    
}

method Main()
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

    var test1 := EOSorted(testArray1);
    assert test1 == true;

    var test2 := EOSorted(testArray2);
    //assert test2 == true;

    var test3 := EOSorted(testArray3);
    //assert test3 == true;

    var test4 := EOSorted(testArray4);
    //assert test4 == true;

    var test5 := EOSorted(testArray5);
    //assert test5 == false;

    print "hellooo\n";
    print test1, "--", test2, "--", test3, "--",test4, "--",test5, "--\n";
}