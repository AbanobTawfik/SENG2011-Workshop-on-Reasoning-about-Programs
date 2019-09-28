method IncDec(x: int, y: int) returns (sum: int)
ensures sum == x + y
{
    sum := x;
    var counter := 0;
    assert sum == x;
    if y > 0
    {
        while counter < y
        invariant counter <= y 
        invariant sum == x + counter;
        {
            counter := counter + 1;
            sum := sum + 1;
        }
        assert counter == y;
    }
    else if y < 0
    {
        while counter > y
        invariant counter >= y
        invariant sum == x + counter;
        {
            counter := counter - 1;
            sum := sum - 1;
        }
        assert counter == y;
    }
    assert sum == x + y;
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