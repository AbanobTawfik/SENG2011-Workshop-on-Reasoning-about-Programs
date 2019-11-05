/////////////////////////////////////////////////////////////
//       ALL CODE IN HERE NOT IN MAIN IS WRITTEN BY        //
//                 ABANOB TAWFIK                           //
//                    Z5075490                             //
//                 November 2019                           //
/////////////////////////////////////////////////////////////

// Ex4.dfy 15 marks
// The national flag of Holland consists of the colours red, white and blue. The monarchy in Holland
// is the House of Orange, and indeed orange is the patriotic colour the Dutch use on days of national
// celebrations. A proposal is made to add the orange colour as a 4th colour to the national flag, so the 4
// colours are red, white, blue and orange, in that order. Update the 3-colour Dutch national-flag problem
// to handle these 4 colours. Note the following:

// • The new 4-colour method should not return any variables. Hence the signature of the method
// should be FlagSort(flag:array<Colour>).
// • A Main() method is provided on the website to verify FlagSort. This method, shown below, calls
// a predicate to verify the flag array is 4-colour sorted. You need to write this predicate yourself.

// inspiration did come from rustan leinos video of himself doing this ESPECIALLY his definition of sorted colours
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
    // same invariant as lecture, but just add a new orange region :)
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
            // if we come accross orange, the first thing we want to do, is decrement both blue and orange section
            // to maintain the ordering blue > orange, we have to move blue down with orange
            // if we dont and have an array with more orange than blue, 
            // our orange region will decrement INFRONT of the blue region
            // first we swap into the orange section, and then we check if our blue section already contains elements
            // it will contain elements if blue is smaller than orange, meaning we hit the case above atleast once which 
            // begins the difference. In the case we have a blue section, we want to swap the value in next into blue
            // to maintain correct ordering. since next hasn't changed, the new value will be handled with one of the cases
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

// due to the way we check each colour, we naturally imply sorting
// start with red, all elements that are red, have no elements behind them that is not red (no white or blue or orange)
// meaning red has its own region and for all red elements, there are no elements behind that are white/blue/orange

// next white, all elements that are white can only have previous elements as red or white (no blue or orange)
// but since we said all elements that are red have no elements behind them that are not red (only red)
// that means the there are no white elements behind red elements, meaning white has its region
// and that for all white elements there are no elements behind that are blue/orange

// next blue, all elements that are blue can only have previous elements are red or white or blue (no orange)
// but since we said all elements that are red have no elements behind them that are not red (only red)
// and from above we said that blue has been partioned so that its seperate from red and has no blue elements behind it
// this means there are no blue elements behind red or white elements, meaning blue has its own region
// and that for all blue  elements there are no elements behind that are orange

// finally this leaves just the orange elements, but since we said that
// there is no orange element behind all red/white/blue elements and that they are in their own regions
// this just leaves the only place orange elements can be is at the end, but this is naturally implied
predicate ColourSorted(flag:array<Colour>)
requires flag != null
reads flag
{
    forall i :: 0 <= i < flag.Length && (flag[i] == RED) ==> !(exists j :: 0 <= j < i && NotRed(flag[j])) &&
    forall i :: 0 <= i < flag.Length && (flag[i] == WHITE) ==> !(exists j :: 0 <= j < i && NotRedWhite(flag[j])) &&
    forall i :: 0 <= i < flag.Length && (flag[i] == BLUE) ==> !(exists j :: 0 <= j < i && NotRedWhiteBlue(flag[j]))
}

// red region essentially means the colour can only be red
// white/blue/orange not accepted
predicate NotRed(color: Colour)
{
    ((color == WHITE) || (color == BLUE) || (color == ORANGE))
}

// red white region means the only colours can be red white
// blue/orange is not accepted
predicate NotRedWhite(color: Colour)
{
    ((color == BLUE) || (color == ORANGE))
}

// red white blue region means the only colours can be red white
// only orange is not accepted
predicate NotRedWhiteBlue(color: Colour)
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