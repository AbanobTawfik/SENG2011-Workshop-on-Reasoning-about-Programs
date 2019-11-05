// inspiration did come from rustan leinos video of himself doing this
// https://www.youtube.com/watch?v=dQC5m-GZYbk
datatype Colour = RED | WHITE | BLUE | ORANGE
method FlagSort(flag:array<Colour>)
modifies flag
ensures multiset(flag[..]) == multiset(old(flag[..]))
ensures ColourSorted(flag)
requires flag != null
{
    var white := 0;
    var next := 0;
    var blue := flag.Length;
    var orange := flag.Length;
    while next < blue
    decreases (orange + blue) - (next + white)
    invariant 0 <= white <= next <= blue <= orange <= flag.Length
    invariant forall i :: 0 <= i < white ==> flag[i] == RED
    invariant forall i :: white <= i < next ==> flag[i] == WHITE
    invariant forall i :: blue <= i < orange ==> flag[i] == BLUE
    invariant forall i :: orange <= i < flag.Length ==> flag[i] == ORANGE
    invariant multiset(flag[..]) == multiset(old(flag[..]))
    {
        match(flag[next])
        {
            // same case of dutch flag with 3 colours, swap the white to the beginning and move the white accross
            case RED     => 
                flag[next], flag[white] := flag[white], flag[next];
                white := white + 1;
                next := next + 1;
            // same case of dutch flag with 3 colours, move along incrementing next
            case WHITE   => 
                next := next + 1;
            // same case of dutch flag with 3 colours, move it to the blue section, and decrement the blue  
            case BLUE    =>
                blue := blue - 1;
                flag[next], flag[blue] := flag[blue], flag[next];
            // new trickier case
            // if we come accross orange, the first thing we want to do, is move it to the orange pointer
            // then we want to check 
            case ORANGE  =>
                blue := blue - 1;
                orange := orange - 1;
                flag[next], flag[orange] := flag[orange], flag[next]; 
                // THIS IS THE KEY TO EVERYTHING TO PARTITION INTO 4 SECTIONS
                // we say the sort is finished when our next is pointing at blue
                // this will account for the pointer change in blue, we change the pointer 
                // to blue to maintain the invariant that the blue section comes before the orange section
                // since this doesn't change the actual value of next, on the next iteration, 
                // the item we just swapped with the blue
                // will be sorted with the cases above, this is just to maintain the invariant that blue < orange
                // this is important since it will maintain the partioning that orange goes infront of blue
                // if we do not correct blue, and just fix orange the sort would not be doing what it's suppose to be doing
                // and we would get the blue elements pointing infront of orange, destroying our ordering
                if(blue < orange)
                {
                    flag[next], flag[blue] := flag[blue], flag[next];
                }
        }
    }
}
// naturally implies that no orange in any of the red/white/white regions since all say not exists orange
predicate ColourSorted(flag:array<Colour>)
requires flag != null
reads flag
{
    forall i :: 0 <= i < flag.Length && (flag[i] == RED) ==> !(exists j :: 0 <= j < i && RedRegion(flag[j])) &&
    forall i :: 0 <= i < flag.Length && (flag[i] == WHITE) ==> !(exists j :: 0 <= j < i && RedWhiteRegion(flag[j])) &&
    forall i :: 0 <= i < flag.Length && (flag[i] == BLUE) ==> !(exists j :: 0 <= j < i && RedWhiteBlueRegion(flag[j]))
}

predicate RedRegion(color: Colour)
{
    ((color == WHITE) || (color == BLUE) || (color == ORANGE))
}

predicate RedWhiteRegion(color: Colour)
{
    ((color == BLUE) || (color == ORANGE))
}

predicate RedWhiteBlueRegion(color: Colour)
{
    color == ORANGE
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