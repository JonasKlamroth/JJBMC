public class ArrayMax {

    /*@

        @ requires a != null;

        @ requires a.length < 5;

        @ ensures (\forall int j; j >= 0 && j < a.length; \result >= a[j]);

        @ ensures a.length > 0 ==>

        @    (\exists int j; j >= 0 && j < a.length; \result == a[j]);

        @ assignable \nothing;

    @*/

	public int max(int[] a) {

		if (a.length == 0) return 0;



		int max = a[0], i = 1;



        /*@

            @ maintaining i >= 1 && i <= a.length;

            @ maintaining (\forall int k; 0 <= k && k < i; max >= a[k]);

            @ maintaining (\exists int j; 0 <= j && j < i; max == a[j]);

            @ decreases a.length - i;

            @ assignable \nothing;

        @*/

		while (i < a.length) {

			if (a[i] > max) max = a[i];

			++i;

		}



		return max;

	}

}