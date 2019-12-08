datatype Colour = RED | WHITE | BLUE | ORANGE

method FlagSort(arr: array<Colour>)
requires arr != null
modifies arr
ensures ColourSorted(arr)
ensures multiset(arr[..]) == multiset(old(arr[..]))
{
    var red := 0;
    var next := 0;
    var blue := arr.Length;
    var orange := arr.Length;
    
    while next < blue
    decreases (orange + blue) - (red + next)
    invariant 0 <= red <= next <= blue <= orange <= arr.Length 
    invariant multiset(arr[..]) == multiset(old(arr[..]))
    invariant forall i :: 0 <= i < red ==> arr[i] == RED
    invariant forall i :: red <= i < next ==> arr[i] == WHITE
    invariant forall i :: blue <= i < orange ==> arr[i] == BLUE
    invariant forall i :: orange <= i < arr.Length ==> arr[i] == ORANGE 
    {
        match arr[next]
        {
            case RED =>
                arr[next], arr[red] := arr[red], arr[next];
                red := red + 1;   
                next := next + 1;       
            case WHITE =>
                next := next + 1;
            case BLUE =>
                blue := blue - 1;
                arr[next], arr[blue] := arr[blue], arr[next];
            case ORANGE => 
                blue := blue - 1;
                orange := orange - 1;
                arr[next], arr[orange] := arr[orange], arr[next];
                if(orange > blue)
                {
                    arr[next], arr[blue] := arr[blue], arr[next];
                }
        }       
    }
}

predicate ColourSorted(arr: array<Colour>)
reads arr
requires arr != null
{
    forall i :: 0 <= i < arr.Length && (arr[i] == RED) ==> RedPartitioned(arr, i) &&
    forall i :: 0 <= i < arr.Length && (arr[i] == WHITE) ==> WhitePartitioned(arr, i) &&
    forall i :: 0 <= i < arr.Length && (arr[i] == BLUE) ==> BluePartitioned(arr, i) 
}

predicate RedPartitioned(arr: array<Colour>, index: int)
reads arr
requires arr != null
requires 0 <= index < arr.Length 
{
    forall i :: 0 <= i < index ==> (arr[i] != WHITE && arr[i] != BLUE && arr[i] != ORANGE)
}

predicate WhitePartitioned(arr: array<Colour>, index: int)
reads arr
requires arr != null
requires 0 <= index < arr.Length 
{
    forall i :: 0 <= i < index ==> (arr[i] != BLUE && arr[i] != ORANGE)
}

predicate BluePartitioned(arr: array<Colour>, index: int)
reads arr
requires arr != null
requires 0 <= index < arr.Length 
{
    forall i :: 0 <= i < index ==> (arr[i] != ORANGE)
}

method Main()
{   // SUBMIT THIS MAIN METHOD WITH YOUR CODE
    var flag: array<Colour> := new Colour[10];
    flag[0], flag[1], flag[2], flag[3] := ORANGE, BLUE, WHITE, RED;
    flag[4], flag[5], flag[6], flag[7] := ORANGE, BLUE, WHITE, RED;
    flag[8], flag[9]                   := RED,    RED;
    assert flag[..] == [ORANGE,BLUE,WHITE,RED,ORANGE,BLUE,WHITE,RED,RED,RED];
    var ms := multiset(flag[..]);
    FlagSort(flag);
    assert ColourSorted(flag);
    assert ms == multiset(flag[..]);
    print flag[..];

    flag := new Colour[0];
    ms := multiset(flag[..]);
    FlagSort(flag);
    assert ColourSorted(flag);
    assert ms == multiset(flag[..]);
    print flag[..], '\n';
}
