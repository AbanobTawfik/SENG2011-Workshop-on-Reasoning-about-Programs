method RotateLeft(arr: array<int>) returns (r: array<int>)
modifies arr
requires arr != null
requires arr.Length > 0
ensures r != null
ensures r.Length == arr.Length
ensures forall i :: 1 <= i < arr.Length ==> r[i - 1] == arr[i]
ensures r[arr.Length - 1] == arr[0]
{
    r := new int[arr.Length];
    var count := 1;
    while count < arr.Length
    invariant 0 <= count <= arr.Length
    invariant forall i :: 1 <= i < count ==> r[i - 1] == arr[i]
    {
        r[count - 1] := arr[count];
        count := count + 1;
    }
    r[arr.Length - 1] := arr[0];
}


method RotateMany(arr: array<int>, amount: int) returns (r: array<int>)
modifies arr
requires arr != null
requires arr.Length > 0
requires 0 <= amount <= arr.Length - 1
ensures r != null
ensures r.Length == arr.Length
ensures forall i :: amount <= i < arr.Length ==> r[i - amount] == arr[i]
ensures forall i :: 0 <= i < amount ==> r[arr.Length + i - amount] == arr[i]
{
    r := new int[arr.Length];
    var count := amount;
    while count < arr.Length
    invariant amount <= count <= arr.Length
    invariant forall i :: amount <= i < count ==> r[i - amount] == arr[i]
    {
        r[count - amount] := arr[count];
        count := count + 1;
    }
    
    forall i | 0 <= i < amount
    {
        r[arr.Length + i - amount] := arr[i];
    }   
}

method RotateMany2(arr: array<int>, amount: int)
modifies arr
requires arr != null
requires arr.Length > 0
requires 0 <= amount <= arr.Length - 1
ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[(i + amount)%arr.Length])
{
    forall i | 0 <= i < arr.Length
    {
        arr[i] := arr[(i + amount)%arr.Length];
    }
}

method RotateMany3(arr: array<int>, amount: int)
modifies arr
requires arr != null
requires arr.Length > 0
requires 0 <= amount <= arr.Length - 1
// ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[(i - amount)%arr.Length])
{
    forall i | 0 <= i < arr.Length
    {
        arr[i] := arr[(i - amount)%arr.Length];
    }
}

method Main()
{
    var a := new int[5];
    a[0], a[1], a[2], a[3], a[4] := 0, 1, 2, 3, 4;
    Print(a);
    RotateMany3(a, 2);
    Print(a);
}

method Print(arr: array<int>)
requires arr != null
ensures multiset(arr[..]) == multiset(old(arr[..]))
{
    var count := 0;
    while count < arr.Length
    invariant 0 <= count <= arr.Length
    invariant multiset(arr[..]) == multiset(old(arr[..]))
    {
        print arr[count], " ";
        count := count + 1;
    }    
    print "\n";
}
