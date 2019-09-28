method Skippy(limit: nat)
{
var skip := 7;
var index := 0;

while index<=limit
invariant index <= limit + skip
invariant index == ((index/skip))*skip
{ index := index+skip; }
assert index >= limit;
assert index == ((index/skip))*skip;
}