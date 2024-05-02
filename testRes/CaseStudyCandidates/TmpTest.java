package CaseStudy;



/**
 * Created by jklamroth on 12/18/18.
 */
public class TmpTest {
    int[] arr;
    int pubInt;

    //@ ensures (\forall int i; 0 <= i && i < \old(arr.length); pubInt == \old(pubInt + arr[i]));
    private void oldTest13() {
        arr[0] += 1;
    }
}

