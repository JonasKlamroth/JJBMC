class BatteryStamps {

    /*@ normal_behaviour
      @  requires 0f <= f < 1000000f;
      @  ensures (float)(int)f <= f < ((float)(int)f) + 1.f;
      @  assignable \nothing;
      @*/
    static void lemma(float f) {
    }
}