public class BinarySearch {

	// binary search where the value sought is known to be in the array
	/*@  requires a != null && a.length >= 1 && a.length <= 5;
	  @  requires (\forall int i; 0<i && i < a.length; a[i-1] <= a[i]);
	  @  requires (\exists int i; 0<=i && i < a.length; a[i] == value);
	  @  requires a[0] <= value && value <= a[a.length-1]; // Redundant, but needed to establish the loop invariant
	  @  ensures a[\result] == value;
	 */
	public int find(int[] a, int value) {
		int lo = 0;
		int hi = a.length -1;
		//@ loop_invariant 0<= lo && lo <= hi && hi < a.length && a[lo] <= value && value <= a[hi];
		//@ decreases hi + 1 - lo;
        //@ loop_modifies lo, hi;
		while (lo < hi) {
			int mid = (lo + hi) / 2;
			//@ assert mid >= lo && mid < hi; // Just checking the prover can do this arithmetic
			//@ assert mid == lo ==> ( lo == hi-1);
			//@ assert mid == lo ==> a[lo] <= a[hi];
			if (a[mid] == value) return mid;
			if (value < a[mid]) {
				hi = mid;
			} else {
				lo = mid;
			}
		}
		return lo;
	}


	// This version correctly fails to prove that hi-lo decreases because if
	//   hi = lo+1 and value is not in the list (so a[lo] < value < a[hi]
	// then mid = lo and we fall through to the else condition in which lo is assigned mid
	// and the loop does not terminate.
	/*@  requires a.length >= 1 && a.length <= 5;
	  @  requires (\forall int i; 0<i && i < a.length; a[i-1] <= a[i]);
	  @  requires a[0] <= value && value <= a[a.length-1]; // Redundant, but needed to establish the loop invariant
	  @  ensures a[\result] == value;
	 */
	public int find1(int[] a, int value) {
		int lo = 0;
		int hi = a.length -1;
		//@ loop_invariant 0<= lo && lo <= hi && hi < a.length && a[lo] <= value && value <= a[hi];
		//@ decreases hi - lo;
		//@ loop_modifies hi, lo;
		while (lo < hi) {
			int mid = (lo + hi) / 2;
			if (a[mid] == value) return mid;
			if (value < a[mid]) {
				hi = mid;
			} else {
				lo = mid;
			}
		}
		return lo;
	}


	// Note - find2 validates and needs both the forall and exists preconditions
	// to do so. However, I'm surprised that this form of stating the quantifications
	// is sufficient for the prover, in the absence of induction
	/*@  requires a.length >= 1 && a.length <= 5;
	  @  requires (\forall int i; 0<i && i < a.length; a[i-1] <= a[i]);
	  @  requires (\exists int i; 0<=i && i < a.length; a[i] == value);
	  @  requires a[0] <= value && value <= a[a.length-1]; // Redundant, but needed to establish the loop invariant
	  @  ensures a[\result] == value;
	 */
	public int find2(int[] a, int value) {
		int lo = 0;
		int hi = a.length -1;
		//@ loop_invariant 0<= lo && lo <= hi && hi < a.length && a[lo] <= value && value <= a[hi];
		//@ decreases hi - lo;
		//@ loop_modifies hi, lo;
		while (lo < hi) {
			int mid = (lo + hi) / 2;
			if (a[mid] == value) return mid;
			if (value < a[mid]) {
				hi = mid;
			} else {
				lo = mid+1;
			}
		}
		return lo;
	}

//	/*@  requires a.length >= 1;
//	  @  requires (\forall int i,j; 0<=i && i<j && j < a.length; a[i] <= a[j]);
//	  @  requires (\exists int i; 0<=i && i < a.length; a[i] == value);
//	  @  requires a[0] <= value && value <= a[a.length-1]; // Redundant, but needed to establish the loop invariant
//	  @  ensures a[\result] == value;
//	 */
//	public int find3(int[] a, int value) {
//		int lo = 0;
//		int hi = a.length -1;
//		//@ loop_invariant 0<= lo && lo <= hi && hi < a.length && a[lo] <= value && value <= a[hi];
//		//@ decreases hi - lo;
//		while (lo < hi) {
//			int mid = (lo + hi) / 2;
//			if (a[mid] == value) return mid;
//			if (value < a[mid]) {
//				hi = mid;
//			} else {
//				lo = mid+1;
//			}
//		}
//		return lo;
//	}
//

}