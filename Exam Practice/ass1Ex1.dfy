method test()
{
    var p: bool;
    var q: bool;
    var r: bool;
    var s: bool;   
    assert true == ((p || q ==> r) && (r ==> s)) ==> (!s ==> !p);
}
