class DishWasher
{
    var HasLoad: bool;
    var HasDetergent: bool;
    var HasWashed: bool;

    predicate Valid()
    reads this`HasLoad
    reads this`HasDetergent
    reads this`HasWashed
    {
        !(HasLoad && HasDetergent && HasWashed) &&
        !(!HasLoad && HasWashed) &&
        !(HasDetergent && HasWashed)
    }

    constructor()
    modifies this`HasLoad
    modifies this`HasDetergent
    modifies this`HasWashed
    ensures Valid()
    ensures (!HasLoad && !HasDetergent && !HasWashed)
    {
        HasLoad := false;
        HasDetergent := false;
        HasWashed := false;
    }
} // end of DishWasher class