public class WrapUtils {

    // Challenge Version, 2nd question.
    
    /*@ public normal_behaviour
      @  requires s != null && lineLength > 0;
      @
      @  requires (\forall int i; 0 <= i && i < s.length; s[i] != '\n');
      @
      @  ensures (\forall int i; 0 <= i && i < s.length;
      @    s[i] == \old(s[i]) || \old(s[i]) == ' ' && s[i] == '\n');
      @
      @  ensures (\forall int a; 0 <= a < s.length;
      @     (\forall int b; a < b < s.length;
      @         (s[a] == '\n' || a == 0) && s[b] == '\n' ==> b-a >= lineLength));
      @
      @  assignable s[*];
      @*/    
    public static void wrapLines(char[] s, int lineLength) {

        int lastBreak = -1;
        int lastSpace = indexOf(s, ' ', 0);

        /*@
          @ loop_invariant lastBreak >= -1 && lastBreak < s.length;
          @ loop_invariant -1 <= lastSpace < s.length;
          @ loop_invariant (\forall int i; 0 <= i < s.length;
          @    s[i] == \old(s[i]) || \old(s[i]) == ' ' && s[i] == '\n');
          @ loop_invariant (\forall int a; 0 <= a < s.length;
          @     (\forall int b; a < b < s.length;
          @         (s[a] == '\n' || a == 0) && s[b] == '\n' ==> b-a >= lineLength));
          @ loop_invariant (\forall int a; lastBreak < a && a < s.length;
          @    s[a] != '\n');
          @ loop_invariant lastSpace != -1 ==> s[lastSpace] == ' ';
          @ decreases lastSpace == -1 ? 0 : s.length + 1 - lastSpace;
          @ loop_modifies s[*], lastBreak, lastSpace;
          @*/
        while(lastSpace != -1) {
            if(lastSpace - lastBreak > lineLength) {
                s[lastSpace] = '\n';
                lastBreak = lastSpace;
            }
            lastSpace = indexOf(s, ' ', lastSpace+1);
        }
    }

    /*@ private normal_behaviour
      @  requires s != null && 0 <= from && from <= s.length;
      @  ensures -1 == \result || from <= \result && \result < s.length;
      @  ensures \result == -1 ==> 
      @     (\forall int i; from <= i && i < s.length; s[i] != c);
      @  ensures \result >= 0 ==>
      @     s[\result] == c && 
      @     (\forall int i; from <= i && i < \result; s[i] != c);
      @  assignable \nothing;
      @*/
    private static /*@ helper */ int indexOf(char[] s, char c, int from) {
        /*@ loop_invariant from <= k && k <= s.length;
          @ loop_invariant (\forall int i; from <= i && i < k; s[i] != c);
          @ decreases s.length - k;
          @ loop_modifies \nothing;
          @*/
        for(int k = from; k < s.length; k++) {
            if(s[k] == c) {
                return k;
            }
        }
        return -1;
    }
}
