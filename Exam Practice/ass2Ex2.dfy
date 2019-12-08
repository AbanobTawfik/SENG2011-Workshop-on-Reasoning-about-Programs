class DishWasher
{
    var loaded: bool;
    var detergent: bool;
    var clean: bool;
    
    predicate Valid()
    reads this
    {
        // empty and dirty impossible!!!
        !(!loaded && !clean)
    }
    
    constructor()
    ensures Valid()
    modifies this
    ensures !loaded && !detergent && clean
    {
        loaded, detergent, clean := false, false, true;
    }
    
    method Load()
    requires Valid() ensures Valid()
    modifies this`loaded, this`clean
    requires !(loaded && clean)
    ensures loaded && !clean
    {
        loaded, clean := true, false;
    }
    
    method AddDtgt()
    requires Valid() ensures Valid()
    modifies this`detergent
    ensures detergent
    {
        detergent := true;
    }
    
    method Wash()
    requires Valid() ensures Valid()
    modifies this`detergent, this`clean
    requires loaded && detergent
    ensures !detergent && clean
    {
        detergent, clean := false, true;
    }
    
    method Unload()
    requires Valid() ensures Valid()
    modifies this`loaded
    requires loaded && clean
    ensures !loaded 
    {
        loaded := false;
    }
}

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
