/*
 * Extended Static Checking Exercise
 * Fall 2013 CSCI181F - Verification-centric Software Engineering
 * Daniel M. Zimmerman
 */



/**
 * A class that represents a quantity of (U.S.) cash in dollars
 * and cents. The quantity can be positive or negative (representing
 * an asset or a debt). Instances of this class are immutable, so it has
 * only queries (and a constructor).
 *
 * @author Daniel M. Zimmerman
 * @version 2013-10-17
 */
/*@ code_bigint_math */
public class CashAmount {

    // invariants for sane amounts of dollars and cents
    //@ public invariant -CENTS_IN_DOLLAR < cents() && cents() < CENTS_IN_DOLLAR;
    //@ public invariant (cents() > 0 ==> dollars() >= 0) && (dollars() > 0 ==> cents() >= 0);
    //@ public invariant (cents() < 0 ==> dollars() <= 0) && (dollars() < 0 ==> cents() <= 0);

    public int maxint = 2147483647;

    /**
     * The number of cents in one dollar.
     */
    public static final int CENTS_IN_DOLLAR = 100;

    /**
     * The number of dollars.
     */
    /*@ spec_public*/private  int my_dollars; //@ in dollars;
    //@ public model int dollars;
    //@ private represents dollars = my_dollars;

    /**
     * The number of cents.
     */
    private  int my_cents; //@ in cents;
    //@ public model int cents;
    //@ private represents cents = my_cents;

    //@ requires -CENTS_IN_DOLLAR < the_cents && the_cents < CENTS_IN_DOLLAR;
    //@ requires (the_cents < 0 ==> the_dollars <= 0) && (the_dollars < 0 ==> the_cents <= 0);
    //@ requires (the_cents > 0 ==> the_dollars >= 0) && (the_dollars > 0 ==> the_cents >= 0);
    //@ ensures dollars() == the_dollars;
    //@ ensures cents() == the_cents;
    /**
     * Constructs a new CashAmount representing the specified amount of cash.
     *
     * @param the_dollars The number of dollars.
     * @param the_cents The number of cents.
     */
    /*@ pure */ public CashAmount(final int the_dollars, final int the_cents) {
        my_dollars = the_dollars;
        my_cents = the_cents;
    }

//    /**
//     * @return a new CashAmount representing the negation of this
//     * CashAmount.
//     */
//    //@ ensures \result.dollars() == -dollars();
//    //@ ensures \result.cents() == -cents();
//    //@ pure
    public CashAmount negate() {
        return new CashAmount(-my_dollars, -my_cents);
    }

    /**
     * Increases this CashAmount by the specified CashAmount.
     *
     * @param the_amount The amount to increase by.
     * @return The resulting CashAmount.
     */
    //@ requires the_amount != null;
    //@ requires maxint - the_amount.dollars > dollars && maxint - the_amount.cents > cents;
    //@ ensures (\result.dollars*CENTS_IN_DOLLAR+\result.cents) ==\old(dollars*CENTS_IN_DOLLAR+cents) + (the_amount.dollars*CENTS_IN_DOLLAR+the_amount.cents);
    //@ pure
    public CashAmount increase(final CashAmount the_amount) {
        int new_dollars = my_dollars + the_amount.my_dollars;
        int new_cents = my_cents + the_amount.my_cents;

        if (new_cents <= -CENTS_IN_DOLLAR) {
            new_cents = new_cents + CENTS_IN_DOLLAR;
            new_dollars = new_dollars - 1;
        }
        if (new_cents >= CENTS_IN_DOLLAR) {
            new_cents = new_cents - CENTS_IN_DOLLAR;
            new_dollars = new_dollars + 1;
        }
        if (new_cents < 0 && new_dollars > 0) {
            new_cents = new_cents + CENTS_IN_DOLLAR;
            new_dollars = new_dollars - 1;
        }
        if (new_cents > 0 && new_dollars < 0) {
            new_cents = new_cents - CENTS_IN_DOLLAR;
            new_dollars = new_dollars + 1;
        }

        return new CashAmount(new_dollars, new_cents);
    }

    //@ requires the_amount != this;
    //@ ensures (dollars*CENTS_IN_DOLLAR+cents) ==\old(dollars*CENTS_IN_DOLLAR+cents) + (the_amount.dollars*CENTS_IN_DOLLAR+the_amount.cents);
    public void add(final CashAmount the_amount) {
        int new_dollars = this.my_dollars + the_amount.my_dollars;
        int new_cents = my_cents + the_amount.my_cents;

        if (new_cents <= -CENTS_IN_DOLLAR) {
            new_cents = new_cents + CENTS_IN_DOLLAR;
            new_dollars = new_dollars - 1;
        }
        if (new_cents >= CENTS_IN_DOLLAR) {
            new_cents = new_cents - CENTS_IN_DOLLAR;
            new_dollars = new_dollars + 1;
        }
        if (new_cents < 0 && new_dollars > 0) {
            new_cents = new_cents + CENTS_IN_DOLLAR;
            new_dollars = new_dollars - 1;
        }
        if (new_cents > 0 && new_dollars < 0) {
            new_cents = new_cents - CENTS_IN_DOLLAR;
            new_dollars = new_dollars + 1;
        }
        my_dollars = new_dollars;
        my_cents = new_cents;

        return;
    }

    // @ requires the_amount != this;
    //@ ensures (dollars*100+cents) ==\old(dollars*100+cents) + (the_amount.dollars*100+the_amount.cents);
    public void addx(final CashAmount the_amount) {
        int new_dollars = this.my_dollars + the_amount.my_dollars;
        int new_cents = my_cents + the_amount.my_cents;

        if (new_cents <= -CENTS_IN_DOLLAR) {
            new_cents = new_cents + CENTS_IN_DOLLAR;
            new_dollars = new_dollars - 1;
        }
        if (new_cents >= CENTS_IN_DOLLAR) {
            new_cents = new_cents - CENTS_IN_DOLLAR;
            new_dollars = new_dollars + 1;
        }
        if (new_cents < 0 && new_dollars > 0) {
            new_cents = new_cents + CENTS_IN_DOLLAR;
            new_dollars = new_dollars - 1;
        }
        if (new_cents > 0 && new_dollars < 0) {
            new_cents = new_cents - CENTS_IN_DOLLAR;
            new_dollars = new_dollars + 1;
        }
        my_dollars = new_dollars;
        my_cents = new_cents;

        return;
    }

    /**
     * Decreases this CashAmount by the specified CashAmount.
     *
     * @param the_amount The amount to decrease by.
     * @return The resulting CashAmount.
     */
    //@ ensures (\result.dollars*100+\result.cents) ==\old(dollars*100+cents) - (the_amount.dollars*100+the_amount.cents);
    public CashAmount decrease(final CashAmount the_amount) {
        return increase(the_amount.negate());
    }

    /**
     * @return The number of dollars in this CashAmount.
     */
    //@ ensures \result == dollars;
    public /*@ pure helper */ int dollars() {
        return my_dollars;
    }

    /**
     * @return The number of cents in this CashAmount.
     */
    //@ ensures \result == cents;
    public /*@ pure helper */ int cents() {
        return my_cents;
    }

    /**
     * Compare this CashAmount with the specified CashAmount for equivalence.
     * Equivalence here means "has exactly the same numbers of dollars and cents."
     *
     * @param the_other The other CashAmount.
     * @return true if the two amounts are equivalent, false otherwise.
     */
    public boolean equivalent(final CashAmount the_other) {
        return the_other.my_dollars == my_dollars && the_other.my_cents == my_cents;
    }
}