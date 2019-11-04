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
    ensures |shadow| == |old(shadow)|
    ensures !(n - m >= 2) ==> shadow == old(shadow)
    ensures (n - m >= 2) ==> shadow == old(shadow[|old(shadow)| - 1..]) + old(shadow[1..|old(shadow)| - 1]) + old(shadow[0..1])
    {
        if n - m >= 2 
        {
            buf[n - 1], buf[m] := buf[m], buf[n-1];
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