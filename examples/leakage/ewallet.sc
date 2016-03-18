
/*
A program that debits a fixed amount from an account until the balance is insufficient. The number of successful debit transactions reveals partial information abount the initial balance.
*/

kind additive3pp;
domain private additive3pp;

// since no leakage besides public inputs and outputs is declared, knowledge inference must prove that declassifying the comparison does not leak additional information.
uint debit (private int balance, uint amount) {
    private uint count = 0;
    
    // a benign value is one that depends on the output
    while (/* @ benign */ declassify(balance >= (int) amount)) // note that this comparison needs to be leaked; SecreC requires public branching decisions
    {
        balance -= amount;
        count += 1;
    }
    return declassify(count);
}