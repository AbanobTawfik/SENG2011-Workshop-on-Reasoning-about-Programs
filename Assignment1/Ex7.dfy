/////////////////////////////////////////////////////////////
//          ALL CODE IN HERE IS WRITTEN BY                 //
//                 ABANOB TAWFIK                           //
//                    Z5075490                             //
//                 September 2019                          //
/////////////////////////////////////////////////////////////

// functions were used to allow for my specification to have 
// functional behaviour e.g. counting
// link to resource: https://www.engr.mun.ca/~theo/Courses/AlgCoCo/6892-downloads/dafny-notes-010.pdf

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
ensures b == (CountOccurences(a, key, a.Length - 1) == 1)
ensures forall i :: 0 <= i < a.Length ==> (a[i] == old(a[i]))
{

    var i := 0;
    var count := 0;
    while i < a.Length
    invariant 0 <= i <= a.Length
    invariant count == CountOccurences(a, key, i-1)
    {
        if(a[i] == key)
        {
            count := count + 1;
        }
        i := i + 1;
    }
    b := (count == 1);
}

// this function will be used to count the number of occurences of the key
// in the array a, up until the index provided
function CountOccurences(a: array<int>, key: int, index: int): int
requires a != null
requires index < a.Length
// short circuit checking first :), this is only really here just so 
// i can perform my assertions on occurences in array, no functional reason
ensures (index >= 0 && a[index] == key) ==> (CountOccurences(a, key, index) == 1 + CountOccurences(a, key, index - 1))
ensures (index >= 0 && a[index] != key) ==> (CountOccurences(a, key, index) ==  CountOccurences(a, key, index - 1))
reads a
// here i supply my variant that maxIndex is decreasing
decreases index
{
    if index < 0 
    then
        0
    else
        if a[index] == key 
        then
            CountOccurences(a, key, index - 1) + 1
        else
            CountOccurences(a, key, index - 1) 
}

predicate VerifyJustOne(a: array<int>, key: int)
requires a != null;
reads a;
{
    (exists i :: 0 <= i < a.Length && a[i] == key) &&
    (forall i,j :: 0 <= i <= j < a.Length && (a[i] == a[j]) && (a[i] == key) ==> i == j)
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
    var test1 := Just1(testArray1, 1);
    assert (CountOccurences(testArray1, 1, testArray1.Length - 1) == 3);
    assert !VerifyJustOne(testArray1, 1);
    assert !test1;

    assert testArray1.Length == 4;
    assert testArray1[0] == 1;
    assert testArray1[1] == 1;
    assert testArray1[2] == 2;
    assert testArray1[3] == 1;
    var test2 := Just1(testArray1, 2);
    assert (CountOccurences(testArray1, 2, testArray1.Length - 1) == 1);
    assert VerifyJustOne(testArray1, 2);
    assert test2;
    
    assert testArray1.Length == 4;
    assert testArray1[0] == 1;
    assert testArray1[1] == 1;
    assert testArray1[2] == 2;
    assert testArray1[3] == 1;
    var test3 := Just1(testArray1, 3);
    assert (CountOccurences(testArray1, 3, testArray1.Length - 1) == 0);
    assert !VerifyJustOne(testArray1, 3);
    assert !test3;

    assert testArray2.Length == 1;
    assert testArray2[0] == 1;
    var test4 := Just1(testArray2, 1);
    assert (CountOccurences(testArray2, 1, testArray2.Length - 1) == 1);
    assert VerifyJustOne(testArray2, 1);
    assert test4;

    assert testArray2.Length == 1;
    assert testArray2[0] == 1;
    var test5 := Just1(testArray2, 2);
    assert (CountOccurences(testArray2, 2, testArray2.Length - 1) == 0);
    assert !VerifyJustOne(testArray2, 2);
    assert !test5;

    assert testArray3.Length == 0;
    var test6 := Just1(testArray3, 1);
    assert (CountOccurences(testArray3, 1, testArray3.Length - 1) == 0);
    assert !VerifyJustOne(testArray3, 1);
    assert !test6;

    print test1, "\n", test2, "\n", test3, "\n", test4, "\n", test5, "\n", test6, "\n";
}