public final class SSSS {
    public static final int BASE_CASE_SIZE = 32;
    public static final int LOG_MAX_BUCKETS = 6;
    public static final int SINGLE_LEVEL_THRESHOLD = BASE_CASE_SIZE * (1 << LOG_MAX_BUCKETS);
    public static final int TWO_LEVEL_THRESHOLD = SINGLE_LEVEL_THRESHOLD * (1 << LOG_MAX_BUCKETS);

    public static final int BUFFER_SIZE = 1024 / 4;

    /* @ public normal_behaviour
      @ ensures \result == ((a >= b) ? a : b);
      @ accessible \nothing;
      @ assignable \strictly_nothing;
      @*/
    public static int max(int a, int b) {
        return (a >= b) ? a : b;
    }

    /* @ public normal_behaviour
      @ ensures \result == ((a <= b) ? a : b);
      @ accessible \nothing;
      @ assignable \strictly_nothing;
      @*/
    public static int min(int a, int b) {
        return (a <= b) ? a : b;
    }

    /* @ public normal_behaviour
      @ requires offset >= 0;
      @
      @ ensures \result == blockAligned(offset);
      @
      @ assignable \strictly_nothing;
      @ accessible \nothing;
      @*/
    public static int align_to_next_block(int offset) {
        return (offset + BUFFER_SIZE - 1) & (-BUFFER_SIZE);
    }


    /* @ public normal_behaviour
      @ requires n > 0;
      @
      @ ensures isLog2Of(n, \result);
      @
      @ assignable \strictly_nothing;
      @*/
    public static int log2(int n) {
        int log = 0;
        if ((n & 0xffff0000) != 0) {
            n >>>= 16;
            log = 16;
        }
        if (n >= 256) {
            n >>>= 8;
            log += 8;
        }
        if (n >= 16) {
            n >>>= 4;
            log += 4;
        }
        if (n >= 4) {
            n >>>= 2;
            log += 2;
        }
        return log + (n >>> 1);
    }

    /* @ public normal_behaviour
      @ requires n >= BASE_CASE_SIZE;
      @
      @ ensures 1 <= \result <= LOG_MAX_BUCKETS;
      @ // Only the lower log bound holds since the function might yield a smaller result
      @ ensures (1 << \result) * BASE_CASE_SIZE <= n;
      @
      @ assignable \strictly_nothing;
      @*/
    public static int log_buckets(int n) {
        if (n <= SINGLE_LEVEL_THRESHOLD) {
            // Only one more level until the base case, reduce the number of buckets
            return max(1, log2(n / BASE_CASE_SIZE));
        } else if (n <= TWO_LEVEL_THRESHOLD) {
            // Only two more levels until we reach the base case, split the buckets
            // evenly
            return max(1, (log2(n / BASE_CASE_SIZE) + 1) / 2);
        } else {
            // Use the maximum number of buckets
            return LOG_MAX_BUCKETS;
        }
    }

    /* @ public normal_behaviour
      @ requires n >= BASE_CASE_SIZE;
      @
      @ ensures \result == log2(n) / 5;
      @
      @ assignable \strictly_nothing;
      @*/
    public static int oversampling_factor(int n) {
        return log2(n) / 5;
    }

    /* @ public model_behaviour
      @ requires n >= BASE_CASE_SIZE;
      @
      @ ensures \result;
      @
      @ static model boolean logLogLemma(int n) {
      @     return oversampling_factor(n) * log2(n / BASE_CASE_SIZE) <= n / 2;
      @ }
      @*/

    private static class SampleResult {
        public final int num_samples;
        public final int num_buckets;
        public final int step;

        public /* @ strictly_pure */ SampleResult(int num_samples, int num_buckets, int step) {
            this.num_samples = num_samples;
            this.num_buckets = num_buckets;
            this.step = step;
        }
    }

    static /*@pure*/ boolean isValidSampleResultForLen(SampleResult r, int n) {

       boolean b1 =          2 <= r.num_samples && r.num_samples <= n / 2;
       boolean b3 =                  r.num_samples < n;
       boolean b4 =                  1 <= r.step;
       boolean b5 =                  2 <= r.num_buckets && r.num_buckets <= 1 << LOG_MAX_BUCKETS;
       boolean b6 =                  r.num_buckets % 2 == 0;
       boolean b8 =                  r.step * r.num_buckets - 1 <= r.num_samples;
       return b1 && b3 && b4 && b5 && b6 && b8;
    }


    /*@ normal_behaviour
      @ requires n >= BASE_CASE_SIZE;
      @
      @ ensures isValidSampleResultForLen(\result, n);
      @ // ensures \fresh(\result);
      @
      @ assignable \nothing;
      @*/
    private static SampleResult sample_parameters(int n) {
        int log_buckets = log_buckets(n);
        int num_buckets = 1 << log_buckets;
        int step = max(1, log2(n) / 5);
        int num_samples = step * num_buckets - 1;

        return new SampleResult(num_samples, num_buckets, step);
    }


    public static void main(String args[]) {
       for (int n = BASE_CASE_SIZE; n > 0; n++) {
            if (!isValidSampleResultForLen(sample_parameters(n), n)) {
                throw new Error("Fails for "+n);
            }
        }
    }
}