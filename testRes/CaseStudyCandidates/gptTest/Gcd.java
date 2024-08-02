// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

public class Gcd {

    /*@ normal_behavior
      @ ensures (a != 0 || b != 0) ==> (a % \result == 0 && b % \result == 0);
      @ assignable \nothing;
      @*/
    public static int gcd(int a, int b) {
        if (a < 0)
            a = -a;
        if (b < 0)
            b = -b;
        int big, small;
        if (a > b) {
            big = a;
            small = b;
        } else {
            big = b;
            small = a;
        }
        return gcdHelp(big, small);
    }

    /*@ private normal_behavior
      @ assignable \nothing;
      @ requires _big <= 100 && _small <= 100;
      @ requires _big >= 0 && _small >= 0;
      @ ensures _big % \result == 0 && _small % \result == 0 &&
      @         (\forall int x; 1 <= x && x <= \result; (_big % x == 0 && _small % x == 0) ==> x == \result);
      @*/
    private static int gcdHelp(int _big, int _small) {
        int big = _big;
        int small = _small;
        {
            /*@ loop_invariant small >= 0 && big >= small &&
              @                 (\forall int x; 1 <= x && x <= big; (_big % x == 0 && _small % x == 0) ==> (big % x == 0 && small % x == 0));
              @ decreases small;
              @ assignable \nothing;
              @*/
            while (small != 0) {
                final int t = big % small;
                big = small;
                small = t;
            }
        }
        return big;
    }

    public static void main(String[] args) {
        System.out.println(gcdHelp(1000, 640));
    }
}
