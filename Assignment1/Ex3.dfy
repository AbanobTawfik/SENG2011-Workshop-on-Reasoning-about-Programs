/////////////////////////////////////////////////////////////
//          ALL CODE IN HERE IS WRITTEN BY                 //
//                 ABANOB TAWFIK                           //
//                    Z5075490                             //
//                 September 2019                          //
/////////////////////////////////////////////////////////////

// Ex3.dfy 3 marks. 

// The following method consists of a simple while statement 
// with a loop variable that starts at 0 and skips to a limit.
// Verify it is correct by filling in the predicates pred1 and pred2.

method Skippy(limit: nat)
{
var skip := 7;
var index := 0;

while index<=limit
// pred 1 
invariant index <= limit + skip
invariant index == ((index/skip))*skip
// end pred 1
{
     index := index+skip; 
}
// pred 2
assert index >= limit;
assert index == ((index/skip))*skip;
// end pred 2
}