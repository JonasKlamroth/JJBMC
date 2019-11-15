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
/*
    Manually applied to all methods
    // invariants for sane amounts of dollars and cents
    //@ public invariant -CENTS_IN_DOLLAR < cents() && cents() < CENTS_IN_DOLLAR;
    //@ public invariant (cents() > 0 ==> dollars() >= 0) && (dollars() > 0 ==> cents() >= 0);
    //@ public invariant (cents() < 0 ==> dollars() <= 0) && (dollars() < 0 ==> cents() <= 0);
*/
    public int maxint = 2147483647;
    public static final int max_val = 10;
    public static final int min_val = -max_val;

    /**
     * The number of cents in one dollar.
     */
    public static final int CENTS_IN_DOLLAR = 100;

    /**
     * The number of dollars.
     */
    public int my_dollars;


    /**
     * The number of cents.
     */
    public int my_cents;


    //@ ensures my_dollars == the_dollars;
    //@ ensures my_cents == the_cents;
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

    public CashAmount() {
        my_cents = 0;
        my_dollars = 0;
    }

    /**
     * @return a new CashAmount representing the negation of this
     * CashAmount.
     *
     * This fails if not excluding maxint+
     */
    //@ requires -CENTS_IN_DOLLAR < my_cents && my_cents < CENTS_IN_DOLLAR;
    //@ requires (my_cents > 0 ==> my_dollars >= 0) && (my_dollars > 0 ==> my_cents >= 0);
    //@ requires (my_cents < 0 ==> my_dollars <= 0) && (my_dollars < 0 ==> my_cents <= 0);
    //@ ensures \result.my_dollars == -my_dollars;
    //@ ensures \result.my_cents == -my_cents;
    //@ pure
    public CashAmount negate() {
        return new CashAmount(-my_dollars, -my_cents);
    }

    /**
     * Increases this CashAmount by the specified CashAmount.
     *
     * @param the_amount The amount to increase by.
     * @return The resulting CashAmount.
     */
    //@ requires my_cents >= min_val && my_cents <= max_val && my_dollars >= min_val && my_dollars <= max_val;
    //@ requires -CENTS_IN_DOLLAR < my_cents && my_cents < CENTS_IN_DOLLAR;
    //@ requires (my_cents > 0 ==> my_dollars >= 0) && (my_dollars > 0 ==> my_cents >= 0);
    //@ requires (my_cents < 0 ==> my_dollars <= 0) && (my_dollars < 0 ==> my_cents <= 0);
    //@ requires the_amount != null;
    //@ requires the_amount.my_cents >= min_val && the_amount.my_cents <= max_val && the_amount.my_dollars >= min_val && the_amount.my_dollars <= max_val;
    //@ requires -CENTS_IN_DOLLAR < the_amount.my_cents && the_amount.my_cents < CENTS_IN_DOLLAR;
    //@ requires (the_amount.my_cents > 0 ==> the_amount.my_dollars >= 0) && (the_amount.my_dollars > 0 ==> the_amount.my_cents >= 0);
    //@ requires (the_amount.my_cents < 0 ==> the_amount.my_dollars <= 0) && (the_amount.my_dollars < 0 ==> the_amount.my_cents <= 0);
    //@ requires Integer.MAX_VALUE - the_amount.my_dollars > my_dollars && Integer.MAX_VALUE - the_amount.my_cents > my_cents;
    //@ ensures (\result.my_dollars*CENTS_IN_DOLLAR+\result.my_cents) ==\old(my_dollars*CENTS_IN_DOLLAR+my_cents) + (the_amount.my_dollars*CENTS_IN_DOLLAR+the_amount.my_cents);
    //@ ensures my_cents >= min_val && my_cents <= max_val && my_dollars >= min_val && my_dollars <= max_val;
    //@ ensures -CENTS_IN_DOLLAR < my_cents && my_cents < CENTS_IN_DOLLAR;
    //@ ensures (my_cents > 0 ==> my_dollars >= 0) && (my_dollars > 0 ==> my_cents >= 0);
    //@ ensures (my_cents < 0 ==> my_dollars <= 0) && (my_dollars < 0 ==> my_cents <= 0);
    //@ ensures the_amount.my_cents >= min_val && the_amount.my_cents <= max_val && the_amount.my_dollars >= min_val && the_amount.my_dollars <= max_val;
    //@ ensures -CENTS_IN_DOLLAR < the_amount.my_cents && the_amount.my_cents < CENTS_IN_DOLLAR;
    //@ ensures (the_amount.my_cents > 0 ==> the_amount.my_dollars >= 0) && (the_amount.my_dollars > 0 ==> the_amount.my_cents >= 0);
    //@ ensures (the_amount.my_cents < 0 ==> the_amount.my_dollars <= 0) && (the_amount.my_dollars < 0 ==> the_amount.my_cents <= 0);
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

    //@ requires my_cents >= min_val && my_cents <= max_val && my_dollars >= min_val && my_dollars <= max_val;
    //@ requires -CENTS_IN_DOLLAR < my_cents && my_cents < CENTS_IN_DOLLAR;
    //@ requires (my_cents > 0 ==> my_dollars >= 0) && (my_dollars > 0 ==> my_cents >= 0);
    //@ requires (my_cents < 0 ==> my_dollars <= 0) && (my_dollars < 0 ==> my_cents <= 0);
    //@ requires the_amount != null;
    //@ requires the_amount.my_cents >= min_val && the_amount.my_cents <= max_val && the_amount.my_dollars >= min_val && the_amount.my_dollars <= max_val;
    //@ requires -CENTS_IN_DOLLAR < the_amount.my_cents && the_amount.my_cents < CENTS_IN_DOLLAR;
    //@ requires (the_amount.my_cents > 0 ==> the_amount.my_dollars >= 0) && (the_amount.my_dollars > 0 ==> the_amount.my_cents >= 0);
    //@ requires (the_amount.my_cents < 0 ==> the_amount.my_dollars <= 0) && (the_amount.my_dollars < 0 ==> the_amount.my_cents <= 0);
    //@ requires Integer.MAX_VALUE - the_amount.my_dollars > my_dollars && Integer.MAX_VALUE - the_amount.my_cents > my_cents;
    //@ ensures (my_dollars*CENTS_IN_DOLLAR+my_cents) ==\old(my_dollars*CENTS_IN_DOLLAR+my_cents) + (the_amount.my_dollars*CENTS_IN_DOLLAR+the_amount.my_cents);
        //@ ensures -CENTS_IN_DOLLAR < my_cents && my_cents < CENTS_IN_DOLLAR;
    //@ ensures (my_cents > 0 ==> my_dollars >= 0) && (my_dollars > 0 ==> my_cents >= 0);
    //@ ensures (my_cents < 0 ==> my_dollars <= 0) && (my_dollars < 0 ==> my_cents <= 0);
    //@ ensures -CENTS_IN_DOLLAR < the_amount.my_cents && the_amount.my_cents < CENTS_IN_DOLLAR;
    //@ ensures (the_amount.my_cents > 0 ==> the_amount.my_dollars >= 0) && (the_amount.my_dollars > 0 ==> the_amount.my_cents >= 0);
    //@ ensures (the_amount.my_cents < 0 ==> the_amount.my_dollars <= 0) && (the_amount.my_dollars < 0 ==> the_amount.my_cents <= 0);
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

    //@ requires my_cents >= min_val && my_cents <= max_val && my_dollars >= min_val && my_dollars <= max_val;
    //@ requires -CENTS_IN_DOLLAR < my_cents && my_cents < CENTS_IN_DOLLAR;
    //@ requires (my_cents > 0 ==> my_dollars >= 0) && (my_dollars > 0 ==> my_cents >= 0);
    //@ requires (my_cents < 0 ==> my_dollars <= 0) && (my_dollars < 0 ==> my_cents <= 0);
    //@ requires the_amount != null;
    //@ requires the_amount.my_cents >= min_val && the_amount.my_cents <= max_val && the_amount.my_dollars >= min_val && the_amount.my_dollars <= max_val;
    //@ requires -CENTS_IN_DOLLAR < the_amount.my_cents && the_amount.my_cents < CENTS_IN_DOLLAR;
    //@ requires (the_amount.my_cents > 0 ==> the_amount.my_dollars >= 0) && (the_amount.my_dollars > 0 ==> the_amount.my_cents >= 0);
    //@ requires (the_amount.my_cents < 0 ==> the_amount.my_dollars <= 0) && (the_amount.my_dollars < 0 ==> the_amount.my_cents <= 0);
    //@ requires Integer.MAX_VALUE - the_amount.my_dollars > my_dollars && Integer.MAX_VALUE - the_amount.my_cents > my_cents;
    //@ ensures (my_dollars*100+my_cents) == \old(my_dollars*100+my_cents) + (the_amount.my_dollars*100+the_amount.my_cents);
    //@ ensures -CENTS_IN_DOLLAR < my_cents && my_cents < CENTS_IN_DOLLAR;
    //@ ensures (my_cents > 0 ==> my_dollars >= 0) && (my_dollars > 0 ==> my_cents >= 0);
    //@ ensures (my_cents < 0 ==> my_dollars <= 0) && (my_dollars < 0 ==> my_cents <= 0);
    //@ ensures -CENTS_IN_DOLLAR < the_amount.my_cents && the_amount.my_cents < CENTS_IN_DOLLAR;
    //@ ensures (the_amount.my_cents > 0 ==> the_amount.my_dollars >= 0) && (the_amount.my_dollars > 0 ==> the_amount.my_cents >= 0);
    //@ ensures (the_amount.my_cents < 0 ==> the_amount.my_dollars <= 0) && (the_amount.my_dollars < 0 ==> the_amount.my_cents <= 0);
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

    //Does not work for now
//    /**
//     * Decreases this CashAmount by the specified CashAmount.
//     *
//     * @param the_amount The amount to decrease by.
//     * @return The resulting CashAmount.
//     */
//    //@ requires my_cents >= min_val && my_cents <= max_val && my_dollars >= min_val && my_dollars <= max_val;
//    //@ requires -CENTS_IN_DOLLAR < my_cents && my_cents < CENTS_IN_DOLLAR;
//    //@ requires (my_cents > 0 ==> my_dollars >= 0) && (my_dollars > 0 ==> my_cents >= 0);
//    //@ requires (my_cents < 0 ==> my_dollars <= 0) && (my_dollars < 0 ==> my_cents <= 0);
//    //@ requires the_amount != null;
//    //@ requires the_amount.my_cents >= min_val && the_amount.my_cents <= max_val && the_amount.my_dollars >= min_val && the_amount.my_dollars <= max_val;
//    //@ requires -CENTS_IN_DOLLAR < the_amount.my_cents && the_amount.my_cents < CENTS_IN_DOLLAR;
//    //@ requires (the_amount.my_cents > 0 ==> the_amount.my_dollars >= 0) && (the_amount.my_dollars > 0 ==> the_amount.my_cents >= 0);
//    //@ requires (the_amount.my_cents < 0 ==> the_amount.my_dollars <= 0) && (the_amount.my_dollars < 0 ==> the_amount.my_cents <= 0);
//    //@ requires Integer.MAX_VALUE - the_amount.my_dollars > my_dollars && Integer.MAX_VALUE - the_amount.my_cents > my_cents;
//    //@ ensures (\result.my_dollars*CENTS_IN_DOLLAR+\result.my_cents) == \old(my_dollars*100+my_cents) - (the_amount.my_dollars*CENTS_IN_DOLLAR+the_amount.my_cents);
//    //@ ensures -CENTS_IN_DOLLAR < my_cents && my_cents < CENTS_IN_DOLLAR;
//    //@ ensures (my_cents > 0 ==> my_dollars >= 0) && (my_dollars > 0 ==> my_cents >= 0);
//    //@ ensures (my_cents < 0 ==> my_dollars <= 0) && (my_dollars < 0 ==> my_cents <= 0);
//    //@ ensures -CENTS_IN_DOLLAR < the_amount.my_cents && the_amount.my_cents < CENTS_IN_DOLLAR;
//    //@ ensures (the_amount.my_cents > 0 ==> the_amount.my_dollars >= 0) && (the_amount.my_dollars > 0 ==> the_amount.my_cents >= 0);
//    //@ ensures (the_amount.my_cents < 0 ==> the_amount.my_dollars <= 0) && (the_amount.my_dollars < 0 ==> the_amount.my_cents <= 0);
//    public CashAmount decrease(final CashAmount the_amount) {
//        return increase(the_amount.negate());
//    }

    /**
     * Compare this CashAmount with the specified CashAmount for equivalence.
     * Equivalence here means "has exactly the same numbers of dollars and cents."
     *
     * @param the_other The other CashAmount.
     * @return true if the two amounts are equivalent, false otherwise.
     */
    //@ requires the_other != null;
    public boolean equivalent(final CashAmount the_other) {
        return the_other.my_dollars == my_dollars && the_other.my_cents == my_cents;
    }
}