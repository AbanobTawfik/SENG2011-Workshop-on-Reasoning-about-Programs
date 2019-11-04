// inspiration did come from rustan leinos video of himself doing this
// https://www.youtube.com/watch?v=dQC5m-GZYbk
datatype Colour = RED | WHITE | BLUE | ORANGE
method FlagSort(flag:array<Colour>)
modifies flag
ensures multiset(flag[..]) == multiset(old(flag[..]))
ensures ColourSorted(flag)
requires flag != null
{
    var red := 0;
    var white := 0;
    var blue := flag.Length - 1;
    var orange := flag.Length - 1;
    
    while red <= orange
    decreases (orange + blue) - (red + white)
    invariant 0 <= red <= white <= blue <= orange < flag.Length
    invariant forall i :: 0 <= i <= red ==> flag[i] == RED
    invariant forall i :: red < i <= white ==> flag[i] == WHITE
    invariant forall i :: white < i <= blue ==> flag[i] == BLUE
    invariant forall i :: blue < i <= orange ==> flag[i] == ORANGE
    {
        match(flag[red])
        {
            case RED     => 
                red := red + 1;
            case WHITE   => 
                flag[red], flag[white] := flag[white], flag[red];
                red := red + 1;
                white := white + 1;
            case BLUE    =>
                flag[red], flag[blue] := flag[blue], flag[red];
                blue := blue - 1;
            case ORANGE  => 
                flag[red], flag[orange] := flag[orange], flag[red];
                orange := orange - 1;
                blue := blue - 1;
        }
    }
}
predicate ColourSorted(flag:array<Colour>)
{
    true
    //forall i :: 0 <= i < flag.Length ==> (flag[i] == RED )
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