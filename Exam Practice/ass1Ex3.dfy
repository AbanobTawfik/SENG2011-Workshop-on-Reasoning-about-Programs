method Skippy(limit: nat)
{
    var skip := 7;
    var index := 0;
    while index<=limit
    invariant index % 7 == 0 && 0 <= index <= skip * ((limit / skip) + 1);
    { 
        index := index+skip; 
    }
    assert index % 7 == 0 && index == skip * (limit/skip + 1);
}
