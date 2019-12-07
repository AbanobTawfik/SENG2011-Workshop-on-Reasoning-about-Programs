method IncDec(x: int, y: int) returns (sum: int)
ensures sum == x + y
{
    sum := x;
    var absoluteY: int := y;
    var incrementor: int := 1;
    if(y < 0)
    {
        absoluteY := -1 * y;
        incrementor := -1;
    }
    var count := 0;
    while count < absoluteY
    invariant 0 <= count <= absoluteY
    invariant sum == x + (count * incrementor)
    {
        sum := sum + incrementor;
        count := count + 1;
    }
}

method Test()
{
    var testValue1 := IncDec(5, 15);
    assert testValue1 == 20;

    var testValue2 := IncDec(5, -15);
    assert testValue2 == -10;

    var testValue3 := IncDec(5, 0);
    assert testValue3 == 5;

    var testValue4 := IncDec(-5, 15);
    assert testValue4 == 10;

    var testValue5 := IncDec(-5, -15);
    assert testValue5 == -20;

    var testValue6 := IncDec(-5, 0);
    assert testValue6 == -5;     
}
