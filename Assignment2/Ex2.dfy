class DishWasher
{
    var HasLoad: bool;
    var HasDetergent: bool;
    var ISClean: bool;

    predicate Valid()
    reads this`HasLoad
    reads this`HasDetergent
    reads this`ISClean
    {
        !(HasLoad && HasDetergent && ISClean) &&
        !(!HasLoad && ISClean) &&
        !(HasDetergent && ISClean)
    }

    constructor()
    modifies this`HasLoad
    modifies this`HasDetergent
    modifies this`ISClean
    ensures Valid()
    ensures (!HasLoad && !HasDetergent && ISClean)
    {
        HasLoad := false;
        HasDetergent := false;
        ISClean := true;
    }

    method Load()
    modifies this
    requires Valid() ensures Valid()
    {
        HasLoad := true;
        ISClean := false;
    }

    method AddDtgt()
    modifies this
    requires Valid() ensures Valid()
    {
        HasDetergent := true;
    }

    method Wash()
    modifies this
    requires HasDetergent
    requires HasLoad
    requires Valid() ensures Valid()
    {
        ISClean := true;
        HasDetergent := false;
    }

    method Unload()
    requires HasLoad
    modifies this
    requires Valid() ensures Valid()
    {
        HasLoad := false;
    }
} // end of DishWasher class