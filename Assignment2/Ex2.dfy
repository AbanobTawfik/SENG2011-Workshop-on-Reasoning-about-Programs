/////////////////////////////////////////////////////////////
//          ALL CODE IN HERE IS WRITTEN BY                 //
//                 ABANOB TAWFIK                           //
//                    Z5075490                             //
//                 November 2019                           //
/////////////////////////////////////////////////////////////

// Ex2.pdf and Ex2.dfy 15 marks
// Typically, using a dishwasher involves loading the dishwasher with dirty dishes and then adding the
// detergent to the dispenser. The dishwasher then washes the dishes clean, using all the detergent in the
// process. The dishwasher can then be unloaded, ready to take a new load. At the start, the dishwasher
// is clean: there are no dishes in the dishwasher and there is no detergent in the dispenser. (Note that
// we are modelling the state of the dishwasher, not the control of the dishwasher by pressing buttons.)

// There are 4 distinct actions above: loading, adding detergent, washing and unloading. There is some
// flexibility in the ordering of the actions, as shown by the following 5 testcases:

// 1. A typical testcase is:
// Load, AddDtgt, Wash, Unload
// where the names correspond to the 4 actions above.

// 2. The detergent could have been added first, so another possible ordering is:
// AddDtgt, Load, Wash, Unload

// 3. You know that you are going to do another wash, you could add the detergent much earlier:
// Load, AddDtgt, Wash, AddDtgt, Unload, Load, Wash, Unload

// 4. If the dishes were really dirty, you may also choose to wash the dishes twice before unloading:
// Load, AddDtgt, Wash, AddDtgt, Wash, Unload

// 5. You may also load the machine a few plates at a time, or add detergent a bit at a time, so these
// actions may be repeated:
// Load, Load, Load, AddDtgt, AddDtgt, Wash, Unload

// An example of ’bad’ behaviour that should fail verification is if the user forgets to add detergent to
// the dispenser (a risk to hygiene). This corresponds to testcase 1 with the action AddDtgt missing.
// Another example is if the user forgets to even load the machine (a waste of electricity and detergent),
// which corresponds to testcase 1 with Load missing. These are other examples of behaviour that should
// be rejected by the Dafny verifier.

// In summary, you are asked to:
// • draw a state-transition diagram that represents the behaviour of the dishwasher.
// • write a specification in Dafny that models the behaviour of the dishwasher described above
// • include a method that tests the 5 testcases above, or as many of these testcases or similar testcases
// as you can manage.
// • include testcases that lead to verification errors, but comment these testcases out so your program
// verifies successfully. Add a comment to each ’bad’ testcase that says why failure is justified.
// • you are not allowed to use the :autocontract attribute in this exercise

class DishWasher
{
    var HasLoad: bool;
    var HasDetergent: bool;
    var IsClean: bool;

    predicate Valid()
    reads this`HasLoad, this`HasDetergent, this`IsClean
    {
        !(!HasLoad && !IsClean)
    }

    constructor()
    modifies this`HasLoad, this`HasDetergent, this`IsClean
    ensures Valid()
    ensures !HasLoad && !HasDetergent && IsClean
    {
        HasLoad := false;
        HasDetergent := false;
        IsClean := true;
    }

    method Load()
    modifies this`HasLoad, this`IsClean
    requires !(IsClean && HasLoad)
    ensures HasLoad && !IsClean
    requires Valid() ensures Valid()
    {
        HasLoad := true;
        IsClean := false;
    }

    method AddDtgt()
    modifies this`HasDetergent
    ensures HasDetergent
    requires Valid() ensures Valid()
    {
        HasDetergent := true;
    }

    method Wash()
    modifies this`HasDetergent, this`IsClean
    requires HasDetergent && HasLoad
    ensures !HasDetergent && IsClean
    requires Valid() ensures Valid()
    {
        HasDetergent := false;
        IsClean := true;
    }

    // note in our state transition diagram we only can call unload after we've finished washing
    // this also makes sense in real life, we don't just take dirty stuff out the dishwasher that's disgusting
    method Unload()
    modifies this`HasLoad
    requires HasLoad && IsClean
    ensures !HasLoad
    requires Valid() ensures Valid()
    {
        HasLoad := false;
    }
} // end of DishWasher class

method Test()
{
    // case 1
    var testCase1: DishWasher := new DishWasher();      // !HasLoad, !HasDetergent, IsClean --> empty
    testCase1.Load();                                   // HasLoad, !HasDetergent, !IsClean --> loaded dirty with no detergent
    testCase1.AddDtgt();                                // HasLoad, HasDetergent, !IsClean  --> Loaded dirty with detergent
    testCase1.Wash();                                   // HasLoad, !HasDetergent, IsClean  --> loaded clean with no detergent
    testCase1.Unload();                                 // !HasLoad, !HasDetergent, IsClean --> empty

    // case 2
    var testCase2: DishWasher := new DishWasher();      // !HasLoad, !HasDetergent, IsClean --> empty
    testCase2.AddDtgt();                                // !HasLoad, HasDetergent, IsClean  --> empty with detergent
    testCase2.Load();                                   // HasLoad, HasDetergent, !IsClean  --> loaded dirty with detergent
    testCase2.Wash();                                   // HasLoad, !HasDetergent, IsClean  --> loaded clean with no detergent
    testCase2.Unload();                                 // !HasLoad, !HasDetergent, IsClean --> empty

    // case 3
    var testCase3: DishWasher := new DishWasher();      // !HasLoad, !HasDetergent, IsClean --> empty
    testCase3.Load();                                   // HasLoad, !HasDetergent, !IsClean --> Loaded dirty with no detergent
    testCase3.AddDtgt();                                // HasLoad, HasDetergent, !IsClean  --> Loaded dirty with detergent
    testCase3.Wash();                                   // HasLoad, !HasDetergent, IsClean  --> Loaded clean with no detergent
    testCase3.AddDtgt();                                // HasLoad, HasDetergent, IsClean   --> Loaded clean with detergent
    testCase3.Unload();                                 // !HasLoad, HasDetergent, IsClean  --> empty with detergent
    testCase3.Load();                                   // HasLoad, HasDetergent, !IsClean  --> loaded dirty with detergent
    testCase3.Wash();                                   // HasLoad, !HasDetergent, IsClean  --> loaded clean with no detergent
    testCase3.Unload();                                 // !HasLoad, !HasDetergent, IsClean --> empty

    // case 4
    var testCase4: DishWasher := new DishWasher();      // !HasLoad, !HasDetergent, IsClean --> empty
    testCase4.Load();                                   // HasLoad, !HasDetergent, !IsClean --> Loaded dirty with no detergent
    testCase4.AddDtgt();                                // HasLoad, HasDetergent, !IsClean  --> Loaded dirty with detergent      
    testCase4.AddDtgt();                                // HasLoad, HasDetergent, !IsClean  --> Loaded dirty with detergent 
    testCase4.Wash();                                   // HasLoad, !HasDetergent, IsClean  --> Loaded clean with no detergent 
    testCase4.Unload();                                 // !HasLoad, !HasDetergent, IsClean --> empty 

    // case 5
    var testCase5: DishWasher := new DishWasher();      // !HasLoad, !HasDetergent, IsClean --> empty
    testCase5.Load();                                   // HasLoad, !HasDetergent, !IsClean --> Loaded dirty with no detergent
    testCase5.Load();                                   // HasLoad, !HasDetergent, !IsClean --> Loaded dirty with no detergent
    testCase5.Load();                                   // HasLoad, !HasDetergent, !IsClean --> Loaded dirty with no detergent
    testCase5.AddDtgt();                                // HasLoad, HasDetergent, !IsClean  --> Loaded dirty with detergent
    testCase5.AddDtgt();                                // HasLoad, HasDetergent, !IsClean  --> Loaded dirty with detergent
    testCase5.Wash();                                   // HasLoad, !HasDetergent, IsClean  --> Loaded clean with no detergent 
    testCase5.Unload();                                 // !HasLoad, !HasDetergent, IsClean --> empty 

    // note these failure cases can be seen in the transition diagram as there is no possible state transition to the last step in the flow
    // failure case 1, washing without detergent
    // error message
    // Dafny program verifier version 1.9.7.30401, Copyright (c) 2003-2016, Microsoft.
    // Ex2.dfy(111,18): Error BP5002: A precondition for this call might not hold.
    // Ex2.dfy(42,13): Related location: This is the precondition that might not hold.
    // Execution trace:
    //     (0,0): anon0

    // Dafny program verifier finished with 12 verified, 1 error

    // var failureTestCase1: DishWasher := new DishWasher();                                      // !HasLoad, !HasDetergent, IsClean --> empty 
    // testCase5.Load();                                                                          // HasLoad, !HasDetergent, !IsClean --> Loaded dirty with no detergent     
    // testCase5.Wash();                                                                          // can't perform wash because !HasDetergent

    // failure case 2, washing without load
    // error message
    // Ex2.dfy(132,25): Error BP5002: A precondition for this call might not hold.
    // Ex2.dfy(42,29): Related location: This is the precondition that might not hold.
    // Execution trace:
    //     (0,0): anon0

    // Dafny program verifier finished with 12 verified, 1 error

    // var failureTestCase2: DishWasher := new DishWasher();                                      // !HasLoad, !HasDetergent, IsClean --> empty   
    // failureTestCase2.AddDtgt();                                                                // !HasLoad, HasDetergent, IsClean --> empty with detergent
    // failureTestCase2.Wash();                                                                   // can't perform wash because !HasLoad 

    // my own failure case 3, unloading right after loading (unloading dirty dishes disgusting)
    // Ex2.dfy(145,27): Error BP5002: A precondition for this call might not hold.
    // Ex2.dfy(54,24): Related location: This is the precondition that might not hold.
    // Execution trace:
    //     (0,0): anon0

    // Dafny program verifier finished with 12 verified, 1 error

    // var failureTestCase3: DishWasher := new DishWasher();                                      // !HasLoad, !HasDetergent, IsClean --> empty
    // failureTestCase3.Load();                                                                   // HasLoad, !HasDetergent, !IsClean --> Loaded dirty with no detergent
    // failureTestCase3.AddDtgt();                                                                // HasLoad, HasDetergent, !IsClean --> Loaded dirty with no detergent  
    // failureTestCase3.Unload();                                                                 // dont unload dirty dishes that is disgusting, unload when clean

    // my own failure case 4, mixing clean and dirty dishes
    // Ex2.dfy(210,25): Error BP5002: A precondition for this call might not hold.
    // Ex2.dfy(74,13): Related location: This is the precondition that might not hold.
    // Execution trace:
    //     (0,0): anon0

    // Dafny program verifier finished with 12 verified, 1 error

    // var failureTestCase3: DishWasher := new DishWasher();                                      // !HasLoad, !HasDetergent, IsClean --> empty
    // failureTestCase3.Load();                                                                   // HasLoad, !HasDetergent, !IsClean --> Loaded dirty with no detergent
    // failureTestCase3.AddDtgt();                                                                // HasLoad, HasDetergent, !IsClean --> Loaded dirty with no detergent  
    // failureTestCase3.Wash();                                                                   // HasLoad, !HasDetergent, IsClean --> Loaded clean with no detergent
    // failureTestCase3.Load();                                                                   // dont mix in dirty dishes with clean dishes
}