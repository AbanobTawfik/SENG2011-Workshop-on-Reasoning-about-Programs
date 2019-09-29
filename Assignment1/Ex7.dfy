/////////////////////////////////////////////////////////////
//          ALL CODE IN HERE IS WRITTEN BY                 //
//         	       ABANOB TAWFIK						   //
//          		  Z5075490 			                   //
//				   September 2019						   //
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
ensures VerifyJustOne(a, key) ==> b
ensures !VerifyJustOne(a, key) ==> !b
ensures b ==> VerifyJustOne(a, key)
ensures !b ==> !VerifyJustOne(a, key)
ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i])
{
    if(a.Length == 0)
    {
        b := false;
        return;
    }
    var i := 0;
    var count := 0;
    while i < a.Length
    invariant 0 <= i <= a.Length
    invariant i == 0 ==> b == false;
    invariant i > 0 ==> (b == ((exists j :: 0 <=  j < i && a[j] == key) &&
                (forall j,k :: 0 <= j <= k < i && (a[j] == a[k]) && (a[j] == key) ==> (j == k))))
    {
        if(a[i] == key)
        {
            count := count + 1;
        }
    }
    b := (count == 1);
}



predicate VerifyJustOne(a: array<int>, key: int)
requires a != null;
reads a;
{
    (exists i :: 0 <= i < a.Length && a[i] == key) &&
    (forall i,j :: 0 <= i <= j < a.Length && (a[i] == a[j]) && (a[i] == key) ==> i == j)
}