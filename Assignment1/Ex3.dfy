method Skippy(limit: nat)
{
var skip := 7;
var index := 0;
while index<=limit
invariant index <= limit + skip 
{ index := index+skip; }
assert index > limit;
}