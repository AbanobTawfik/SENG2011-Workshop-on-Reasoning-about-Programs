/////////////////////////////////////////////////////////////
//          ALL CODE IN HEADTAIL IS WRITTEN BY             //
//                 ABANOB TAWFIK                           //
//                    Z5075490                             //
//                 November 2019                           //
/////////////////////////////////////////////////////////////

// Ex3.dfy 10 marks
// In lectures, the verification of a Quack data type was shown (Week 6 lecture, slide 30). You will observe
// that the test method for the quack calls a method called HeadTail() that is missing from the lecture
// notes. This method swaps the data items at the two ends of the queue (so the item at the head goes
// to the tail, and the tail goes to the head). No arguments are returned.
// Implement this method, verifying its correctness using the ghost sequence shadow. The verified code
// for the Quack class and its test method Main() can be found on the website.

class {:autocontracts} Quack<Data>
{
    var buf: array<Data>;
    var m: int, n: int;

    ghost var shadow: seq<Data>;

    predicate Valid()
    { buf!=null && buf.Length!=0 && 0<=m<=n<=buf.Length && shadow==buf[m..n] }

    constructor(size: int)
    requires size>0;
    ensures shadow == [];
    ensures fresh(buf);
    {   buf := new Data[size];
        m, n:= 0, 0;
        shadow:= [];
    }

    method Empty() returns (x: bool)
    ensures x <==> shadow==[]
    { x := m==n; }

    method Pop() returns(x: Data) // + Push() works as a stack
    requires buf != null  // version 1.9.7
    requires shadow != [] 
    ensures       x == old(shadow)[|old(shadow)|-1] // get tail
    ensures  shadow == old(shadow)[..|old(shadow)|-1]
    {   x, n:= buf[n-1], n-1;
        shadow:= shadow[..|shadow|-1];
    }

    method Qop() returns(x: Data) // + Push() works as a queue
    requires buf != null  // version 1.9.7
    requires shadow != [];
    ensures       x == old(shadow)[0] // get head
    ensures  shadow == old(shadow)[1..]
    {   x, m:= buf[m], m+1;
        shadow:= shadow[1..];
    }

    method Push(x: Data)  // + Pop():a stack,  + Qop():a queue
    requires buf != null  // version 1.9.7
    ensures shadow == old(shadow) + [x]; // new tail
    {   if n==buf.Length
        {   var b:= new Data[buf.Length];
            if m==0 { b:= new Data[2*buf.Length]; }
            forall (i | 0<=i<n-m) { b[i]:= buf[m+i]; }
            buf, m, n:= b, 0, n-m;
        }
        buf[n], n:= x, n+1;
        shadow:= shadow + [x];
    }   

    method HeadTail()
    requires buf != null  // version 1.9.7
    // no change in size
    ensures |shadow| == |old(shadow)|
    // if the size of our quack is between 0 and 2, then we just leave it alone
    // headtail for 0 or 1 element should do nothing
    ensures !(n - m >= 2) ==> shadow == old(shadow)
    // we take the tail and make it the head, append everything else to the array, then we take the head and make it the tail
    // this also ensures nothing else changes but head/tail
    ensures (n - m >= 2) ==> shadow == old(shadow[|old(shadow)| - 1..]) + old(shadow[1..|old(shadow)| - 1]) + old(shadow[0..1])
    {
        // only do anything if our quack is of size bigger than 2, (n - m) is size of the array
        if n - m >= 2 
        {
            // swap the head and tail
            buf[n - 1], buf[m] := buf[m], buf[n-1];
            // reconstruct the ghost taking the old tail and making it the new head
            // we then add everything else inbetween except the tail
            // we then take the old head and make it the new tail
            shadow := shadow[|shadow| - 1..] + shadow[1..|shadow| - 1] + shadow[0..1];
        }
    }
} // end of Quack class

method Main()
{   var q:= new Quack<char>(10);
    var l: char;
    q.Push('r'); q.Push('s'); q.Push('k'); q.Push('o'); q.Push('w');
    l:= q.Pop(); print l;  
    q.HeadTail();
    l:= q.Qop(); print l;
    l:= q.Pop(); print l;
    q.HeadTail();
    l:= q.Qop(); print l;    
    l:= q.Qop(); print l;        
    var e: bool:= q.Empty();
    if e {print "\nqueue empty\n";} else {print "\nqueue not empty\n";}
}