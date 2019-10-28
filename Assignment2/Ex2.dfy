class Actuator
{
    var SwitchOn: bool;
    var SwitchOff: bool;

    predicate Valid()
    reads this`SwitchOn
    reads this`SwitchOff
    {
        SwitchOn == !SwitchOff
    }

    constructor()
    modifies this`SwitchOn
    modifies this`SwitchOff
    ensures Valid()
    ensures !SwitchOn && SwitchOff
    {
        SwitchOn := false;
        SwitchOff := true;
    }

    method ToggleSwitch()
    modifies this`SwitchOn
    modifies this`SwitchOff
    requires Valid() ensures Valid()
    ensures (SwitchOn == !old(SwitchOn)) && (SwitchOff == !old(SwitchOff))
    {
        SwitchOn := !SwitchOn;
        SwitchOff := !SwitchOff;
    }
} // end of Actuator class