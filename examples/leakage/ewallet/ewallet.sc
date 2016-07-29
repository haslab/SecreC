
uint debit (uint balance, uint amount) {
    uint count = 0;
    
    while (balance >= amount)
    {
        count = count + 1;
    }
    return count;
}


//predicate PublicIn<T> (x: T)
//predicate PublicOut<T> (x: T)
//predicate PublicMid<T> (x: T)
//predicate DeclassifiedIn<T> (x: T)    
//predicate DeclassifiedOut<T> (x: T)
//predicate Leak<T> (x: T)
//
//method debit (balance: nat, amount: nat) returns (r: nat)
//requires amount < 10;
//requires balance < 10;
//requires amount > 0;
//{
//    var count: nat := 0;
//    var bal: nat := balance;
//    var cmp: bool;
//    var cmp2: bool;
//    var n:nat := balance / amount;
//    assume(Leak(n));
//    
//    while (true)
//    decreases bal
//    invariant Leak(count);
//    invariant 0 <= count <= n
//    invariant bal == balance - amount * count
//    {
//        cmp := bal >= amount;
//        assert(DeclassifiedIn(cmp));
//        if (!cmp) {break;}
//        bal := bal - amount;
//        count := count + 1;
//    }
//    r := count;
//    assert(DeclassifiedIn(r));
//    return;
//}