class Quack<Data>
{
    var buf: array<Data>;
    var m: int, n: int;

    ghost var shadow: seq<Data>;

    predicate Valid() reads this, this.buf
    { buf!=null && buf.Length!=0 && 0<=m<=n<=buf.Length && shadow==buf[m..n] }

    constructor(size: int) modifies this
    requires size>0;
    ensures shadow == []
    ensures fresh(buf)
    ensures Valid()
    {   buf := new Data[size];
        m, n:= 0, 0;
        shadow:= [];
    }
    method Empty() returns (x: bool)
    ensures x <==> shadow==[]
    requires Valid(); ensures Valid()
    { x := m==n; }

    method Pop() returns(x: Data) modifies this, this`n
    requires buf!=null && Valid()
    requires shadow != [] 
    ensures Valid();
    ensures       x  == old(shadow[|old(shadow)|-1])  // get tail
    ensures   shadow == old(shadow[..|old(shadow)|-1])// chop off tail
    ensures |shadow| == |old(shadow)|-1
    ensures buf == old(buf)  // no change to buf here
    {   x, n:= buf[n-1], n-1;
        shadow:= shadow[..|shadow|-1];
    }

    method Qop() returns(x: Data) modifies this, this`m
    requires buf!=null && Valid()
    requires shadow != [];
    ensures Valid();
    ensures        x == old(shadow[0])   // get head
    ensures   shadow == old(shadow[1..]) // chop off head
    ensures |shadow| == |old(shadow)|-1
    ensures buf == old(buf)  // no change to buf here
    {   x, m:= buf[m], m+1;
        shadow:= shadow[1..];
    }

    method Push(x: Data) modifies this, this.buf, this`m, this`n
    requires buf!=null && Valid();
    ensures   shadow == old(shadow) + [x]; // new tail
    ensures |shadow| == |old(shadow)|+1
    ensures if old(n)==old(buf.Length) then fresh(buf) else buf==old(buf)
    ensures Valid();
    {   if n==buf.Length
        {   var b:= new Data[buf.Length];             // temporary
            if m==0 { b:= new Data[2*buf.Length]; }   // double size
            forall (i | 0<=i<n-m) { b[i]:= buf[m+i]; }// copy m..n to 0..n-m
            buf, m, n:= b, 0, n-m;                    // copy b to buf, reset m,n
        }
        buf[n], n:= x, n+1;         // now we definitely have room
        shadow:= shadow + [x];      // same as previous slide: concat 'x'
    }   

    method HeadTail()  modifies this.buf, this`shadow
    requires buf != null && Valid()  // version 1.9.7
    ensures Valid()
    // no change in size
    ensures m == old(m) && n == old(n)
    ensures multiset(buf[..]) == multiset(old(buf[..])) && multiset(shadow) == multiset(old(shadow))
    // note i could also include in here that buf[n - 1] == old(buf[m]) && buf[m] == old(buf[n - 1])
    // and in the else, buf == old(buf), having post conditions on the buf
    // but this slows down verification to over a minute, and it is also implied since shadow REFLECT the buf
    // in the invariant, so we can imply the changes to buf are SHOWN also in the shadow
    ensures if n - m >= 2 then (shadow == (old(shadow[|old(shadow)| - 1..]) + old(shadow[1..|old(shadow)| - 1]) + old(shadow[0..1])))
                          else shadow == old(shadow)
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

method Main() // Dafny 1.9.7
{   var q:= new Quack<char>(10);
    var l: char;
    q.Push('r'); q.Push('s'); q.Push('k'); q.Push('o'); q.Push('w');
    l:= q.Pop(); assert l=='w'; print l;  
    q.HeadTail();
    l:= q.Qop(); assert l=='o'; print l;
    l:= q.Pop(); assert l=='r'; print l;
    q.HeadTail();
    l:= q.Qop(); assert l=='k'; print l;    
    q.HeadTail();
    l:= q.Qop(); assert l=='s'; print l;        
    var e: bool:= q.Empty();
    if e {print "\nqueue empty\n";} else {print "\nqueue not empty\n";}
}