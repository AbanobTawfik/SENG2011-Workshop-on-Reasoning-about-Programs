/////////////////////////////////////////////////////////////
//          ALL CODE IN HERE IS WRITTEN BY                 //
//                 ABANOB TAWFIK                           //
//                    Z5075490                             //
//                 September 2019                          //
/////////////////////////////////////////////////////////////

// Ex7.dfy 10 marks. 
// Write a Dafny method Just1;
// This method should return true if and only if the array contains just one instance of the key. 
// It should return false otherwise.
// Write a test method Main that calls Just1 to verify whether the following arrays contain just one
// instance of the given key:
// • array [1,1,2,1] for the key 1
// • array [1,1,2,1] for the key 2
// • array [1,1,2,1] for the key 3
// • array [1] for the key 1
// • array [1] for the key 2
// • the empty array for the key 1

// and prints the corresponding results:
// False
// True
// False
// True
// False
// False

method Just1(a: array<int>, key: int) returns (b: bool)
requires a != null
ensures b == (CountOccurences(a[0..a.Length], key) == 1)
ensures forall i :: 0 <= i < a.Length ==> (a[i] == old(a[i]))
{
    // note we did not do an initial assumption like Ex6
    // since we are tackling a different problem
    var i := 0;
    var count := 0;
    while i < a.Length
    invariant 0 <= i <= a.Length
    // this invariant says that our running counter
    // should match the number of occurences
    // found in a multiset created from the sequence a
    // up until the index i
    invariant count == CountOccurences(a[0..i], key)
    {
        // if we encounter a key increment our counter by 1
        if(a[i] == key)
        {
            count := count + 1;
        }
        i := i + 1;
    }
    // so now we just return the statement that 
    // count == 1
    b := (count == 1);
}

// this function will take in a sequence and 
// create a multi-set from the sequence
// it will then return the occurences of the key within
// the multiset, all handled by the good old duck Dafny
function CountOccurences(a: seq<int>, key: int): int 
ensures CountOccurences(a, key) == multiset(a)[key]
{
    multiset(a)[key]
}

method Main()
{
    var testArray1: array<int> := new int[4];
    testArray1[0], testArray1[1], testArray1[2],testArray1[3] := 1, 1, 2, 1;
    var testArray2: array<int> := new int[1];
    testArray2[0] := 1;
    var testArray3: array<int> := new int[0];

    assert testArray1.Length == 4;
    assert testArray1[0] == 1;
    assert testArray1[1] == 1;
    assert testArray1[2] == 2;
    assert testArray1[3] == 1;

    assert testArray2.Length == 1;
    assert testArray2[0] == 1;

    assert testArray3.Length == 0;

    var test1 := Just1(testArray1, 1);
    assert CountOccurences(testArray1[0..testArray1.Length], 1) == 3;
    assert !test1;


    var test2 := Just1(testArray1, 2);
    assert CountOccurences(testArray1[0..testArray1.Length], 2) == 1;
    assert test2;
    
    var test3 := Just1(testArray1, 3);
    assert CountOccurences(testArray1[0..testArray1.Length], 3) == 0;
    assert !test3;

    var test4 := Just1(testArray2, 1);
    assert CountOccurences(testArray2[0..testArray2.Length], 1) == 1;
    assert test4;

    var test5 := Just1(testArray2, 2);
    assert CountOccurences(testArray2[0..testArray2.Length], 2) == 0;
    assert !test5;

    var test6 := Just1(testArray3, 1);
    assert CountOccurences(testArray3[0..testArray3.Length], 1) == 0;
    assert !test6;

    print test1, "\n", test2, "\n", test3, "\n", test4, "\n", test5, "\n", test6, "\n";

}