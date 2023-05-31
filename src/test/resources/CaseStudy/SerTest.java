
class SerTest {
    public static byte[] serialize(int i) {
        return new byte[] {
                (byte)(i >> 24),
                (byte)(i >> 16),
                (byte)(i >> 8),
                (byte)i };
    }

    public static int deserialize(byte[] b) {
        return ((b[0] & 0xFF) << 24) |
                ((b[1] & 0xFF) << 16) |
                ((b[2] & 0xFF) << 8 ) |
                ((b[3] & 0xFF) << 0 );
    }


    /*@
      @ public normal_behaviour
      @ ensures i == \result;
      @ assignable \nothing;
      @*/
    public int test(int i) {
        byte[] ser = serialize(i);
        int res = deserialize(ser);
        return res;
    }
}
