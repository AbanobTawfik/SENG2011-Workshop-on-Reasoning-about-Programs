datatype List<T> = empty(T) | next(T, List<T>)

function SumList(list: List<int>): int
ensures SumList(list) == match list case empty(val) => val case next(val, node) => val + SumList(node)
{
    match list
    {
        case empty(val) => val
        case next(val, node) => val + SumList(node)
    }
}

method Main()
{
    var tail: List<int> :=  empty(3);
    var taill: List<int> :=  next(4, tail);
    var head: List<int> :=  next(-69, taill);
    
    assert SumList(head) == -62;
    assert SumList(taill) == 7;
    assert SumList(tail) == 3;
}
