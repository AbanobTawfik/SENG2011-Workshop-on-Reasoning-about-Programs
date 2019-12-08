method SumArray(arr: array<int>) returns (sum: int)
requires arr != null
ensures multiset(arr[..]) == multiset(old(arr[..]))
ensures sum == Sum(arr, arr.Length)
{
    var count := 0;
    sum := 0;
    while count < arr.Length
    invariant 0 <= count <= arr.Length
    invariant sum == Sum(arr, count)
    {
        sum := sum + arr[count];
        count := count + 1;
    }
}

function Sum(arr: array<int>, index: int): int
reads arr
requires arr != null
requires 0 <= index <= arr.Length
ensures if index == 0 then Sum(arr, index) ==  0
                      else Sum(arr, index) == arr[index - 1] + Sum(arr, index - 1)
{
    if index == 0
    then   
        0
    else
        arr[index - 1] + Sum(arr, index - 1)   
    
}
