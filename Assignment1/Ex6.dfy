/////////////////////////////////////////////////////////////
//          ALL CODE IN HERE IS WRITTEN BY                 //
//         	       ABANOB TAWFIK						   //
//          		  Z5075490 			                   //
//				   September 2019						   //
/////////////////////////////////////////////////////////////

// Ex6.dfy 6 marks. 
// Write a Dafny method IsClean:
// The method returns true if and only if the array is clean: 
// that is, if there are no instances of the integer
// key in the array a. The array is considered unclean, hence clean is false, 
// if there are one or more instances of the key in the array.
// Write a test method Main that calls IsClean to verify whether the following arrays are clean of the
// given key:
// • array [1,2,2,2,3] for the key 1
// • array [1,2,2,2,3] for the key 2
// • array [1,2,2,2,3] for the key 3
// • array [1,2,2,2,3] for the key 4
// • array [1] for the key 1
// • array [1] for the key 2
// • the empty array for the key 1

// and prints the corresponding results:
// False
// False
// False
// True
// False
// True
// True

method IsClean(a: array<int>, key: int) returns (clean: bool)
requires a != null
ensures VerifyCleanArray(a, key) ==> clean
ensures !VerifyCleanArray(a, key) ==> !clean
{
    clean := true;
    var i := 0;
    while i < a.Length
    invariant 0 <= i < a.Length
    invariant clean == forall j :: 0 <= i < j ==> a[j] != key
    {
        if(a[i] == key){
            clean := false;
        }
        i := i + 1;
    }
}

predicate VerifyCleanArray(a: array<int>, key: int)
requires a != null;
reads a;
ensures forall i :: 0 <= i < a.Length ==> (a[i] != key) ==> true ==> 
                (exists i :: 0 <= i < a.Length && a[i] == key) ==> false
{
    forall i :: 0 <= i < a.Length ==> (a[i] != key) ==> 
                (!exists i :: 0 <= i < a.Length && a[i] == key)
}

method Main()
{

}