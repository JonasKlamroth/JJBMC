//package sv_esc_solutions;

/*
  This assignment illustrates how specifications (esp invariants and
  preconditions)  written in a formal language can help in removing
  errors in code.

  The assignment concerns a class "Taxpayer" that is used for taxpayers.

 */
/*@ code_bigint_math */
class Taxpayer {

    /* Part 1 of exercise. */

    // public invariant isFemale <==> !isMale;
    // public invariant (isFemale && isMarried) ==> (spouse != null && spouse.isMale);
    // public invariant (isMale   && isMarried) ==> (spouse != null && spouse.isFemale);
    // public invariant isMarried ==> (spouse != null && true && spouse.isMarried);

    /* Part 2 & 3 of exercise. */

    //@ public invariant (!isMarried && age < 65) ==> tax_allowance == DEFAULT_ALLOWANCE;
    //@ public invariant (!isMarried && age >= 65) ==> tax_allowance == ALLOWANCE_OAP;
 /*@ public invariant this.isMarried ==>
   @		   ((tax_allowance + spouse.tax_allowance == 2 * DEFAULT_ALLOWANCE <==> (age < 65  && spouse.age < 65))  ||
   @			(tax_allowance + spouse.tax_allowance == 2 * ALLOWANCE_OAP	 <==> (age >= 65 && spouse.age >= 65)) ||
   @			(tax_allowance + spouse.tax_allowance == DEFAULT_ALLOWANCE + ALLOWANCE_OAP));
   @*/

    /* FIELDS */

    /* isFemale is true iff the person is female */
    /*@ spec_public @*/ boolean isFemale;

    /* isMale is true iff the person is male */
    /*@ spec_public @*/ boolean isMale;

    Taxpayer father, mother; // These fields won't really be used until
    // the next part of the exercise.

    /* Age in years */
    /*@ spec_public @*/ int age;

    /*@ spec_public @*/ boolean isMarried;

    /* Reference to spouce if person is married, null otherwise */
    /*@ spec_public nullable @*/ Taxpayer spouse;

    /* Constant default income tax allowance (belastingvrije som) */
    /*@ spec_public @*/ static final int DEFAULT_ALLOWANCE = 5000;

    /* Constant income tax allowance for Old Age Pensioners over 65 */
    /*@ spec_public @*/ static final  int ALLOWANCE_OAP = 7000;

    /* Income tax allowance (belastingvrije som) */
    /*@ spec_public @*/ int tax_allowance;

    /* Income per year */
    int income;

    /* CONSTRUCTOR */

    Taxpayer(boolean jongetje, Taxpayer ma, Taxpayer pa) {
        age = 0;
        isMarried = false;
        this.isMale = jongetje;
        this.isFemale = !jongetje;
        mother = ma;
        father = pa;
        spouse = null;
        income = 0;
        tax_allowance = DEFAULT_ALLOWANCE;
    }

    /* METHODS */

    /* Marry to new_spouse */
    //@ requires new_spouse != null;
    //@ requires new_spouse.spouse != null;
    //@ requires (!new_spouse.isMarried && new_spouse.age < 65) ==> new_spouse.tax_allowance == DEFAULT_ALLOWANCE;
    //@ requires (!new_spouse.isMarried && new_spouse.age >= 65) ==> new_spouse.tax_allowance == ALLOWANCE_OAP;
 /*@ requires new_spouse.isMarried ==>
   @		   ((new_spouse.tax_allowance + new_spouse.spouse.tax_allowance == 2 * DEFAULT_ALLOWANCE <==> (new_spouse.age < 65  && new_spouse.spouse.age < 65))  ||
   @			(new_spouse.tax_allowance + new_spouse.spouse.tax_allowance == 2 * ALLOWANCE_OAP	 <==> (new_spouse.age >= 65 && new_spouse.spouse.age >= 65)) ||
   @			(new_spouse.tax_allowance + new_spouse.spouse.tax_allowance == DEFAULT_ALLOWANCE + ALLOWANCE_OAP));
   @*/
    //@ requires isFemale <==> !isMale;
    //@ requires (isFemale && isMarried) ==> (spouse != null && spouse.isMale);
    //@ requires (isMale   && isMarried) ==> (spouse != null && spouse.isFemale);
    //@ requires isMarried ==> (spouse != null && true && spouse.isMarried);
    //@ requires !isMarried && !new_spouse.isMarried;
    //@ requires isFemale ==> new_spouse.isMale;
    //@ requires isMale ==> new_spouse.isFemale;
    //@ requires (!isMarried && age < 65) ==> tax_allowance == DEFAULT_ALLOWANCE;
    //@ requires (!isMarried && age >= 65) ==> tax_allowance == ALLOWANCE_OAP;
 /*@ requires this.isMarried ==>
   @		   ((tax_allowance + spouse.tax_allowance == 2 * DEFAULT_ALLOWANCE <==> (age < 65  && spouse.age < 65))  ||
   @			(tax_allowance + spouse.tax_allowance == 2 * ALLOWANCE_OAP	 <==> (age >= 65 && spouse.age >= 65)) ||
   @			(tax_allowance + spouse.tax_allowance == DEFAULT_ALLOWANCE + ALLOWANCE_OAP));
   @*/
    //@ ensures isFemale <==> !isMale;
    //@ ensures (isFemale && isMarried) ==> (spouse != null && spouse.isMale);
    //@ ensures (isMale   && isMarried) ==> (spouse != null && spouse.isFemale);
    //@ ensures isMarried ==> (spouse != null && true && spouse.isMarried);
    //@ ensures (!isMarried && age < 65) ==> tax_allowance == DEFAULT_ALLOWANCE;
    //@ ensures (!isMarried && age >= 65) ==> tax_allowance == ALLOWANCE_OAP;
 /*@ ensures this.isMarried ==>
   @		   ((tax_allowance + spouse.tax_allowance == 2 * DEFAULT_ALLOWANCE <==> (age < 65  && spouse.age < 65))  ||
   @			(tax_allowance + spouse.tax_allowance == 2 * ALLOWANCE_OAP	 <==> (age >= 65 && spouse.age >= 65)) ||
   @			(tax_allowance + spouse.tax_allowance == DEFAULT_ALLOWANCE + ALLOWANCE_OAP));
   @*/
    void marry(Taxpayer new_spouse) {
        spouse = new_spouse;
        isMarried = true;
        new_spouse.spouse = this;		//-------------------------------------------> ADDED (Part 1)
        new_spouse.isMarried = true;	//-------------------------------------------> ADDED (Part 1)
    }

    /* Divorce from current spouse */
    //@ requires isFemale <==> !isMale;
    //@ requires (isFemale && isMarried) ==> (spouse != null && spouse.isMale);
    //@ requires (isMale   && isMarried) ==> (spouse != null && spouse.isFemale);
    //@ requires isMarried ==> (spouse != null && spouse.isMarried);
    //@ requires isMarried;
    //@ requires (!isMarried && age < 65) ==> tax_allowance == DEFAULT_ALLOWANCE;
    //@ requires (!isMarried && age >= 65) ==> tax_allowance == ALLOWANCE_OAP;
 /*@ requires this.isMarried ==>
   @		   ((tax_allowance + spouse.tax_allowance == 2 * DEFAULT_ALLOWANCE <==> (age < 65  && spouse.age < 65))  ||
   @			(tax_allowance + spouse.tax_allowance == 2 * ALLOWANCE_OAP	 <==> (age >= 65 && spouse.age >= 65)) ||
   @			(tax_allowance + spouse.tax_allowance == DEFAULT_ALLOWANCE + ALLOWANCE_OAP));
   @*/
    //@ ensures isFemale <==> !isMale;
    //@ ensures (isFemale && isMarried) ==> (spouse != null && spouse.isMale);
    //@ ensures (isMale   && isMarried) ==> (spouse != null && spouse.isFemale);
    //@ ensures isMarried ==> (spouse != null && true && spouse.isMarried);
    //@ ensures (!isMarried && age < 65) ==> tax_allowance == DEFAULT_ALLOWANCE;
    //@ ensures (!isMarried && age >= 65) ==> tax_allowance == ALLOWANCE_OAP;
 /*@ ensures this.isMarried ==>
   @		   ((tax_allowance + spouse.tax_allowance == 2 * DEFAULT_ALLOWANCE <==> (age < 65  && spouse.age < 65))  ||
   @			(tax_allowance + spouse.tax_allowance == 2 * ALLOWANCE_OAP	 <==> (age >= 65 && spouse.age >= 65)) ||
   @			(tax_allowance + spouse.tax_allowance == DEFAULT_ALLOWANCE + ALLOWANCE_OAP));
   @*/
    void divorce() {
        if (this.age < 65) this.tax_allowance = DEFAULT_ALLOWANCE;		//-------> ADDED (Part 2 & 3)
        else this.tax_allowance = ALLOWANCE_OAP;							//-------> ADDED (Part 2 & 3)
        if (spouse.age < 65) spouse.tax_allowance = DEFAULT_ALLOWANCE;	//-------> ADDED (Part 2 & 3)
        else spouse.tax_allowance = ALLOWANCE_OAP;						//-------> ADDED (Part 2 & 3)
        //@ assert spouse != null;
        spouse.spouse = null;
        spouse.isMarried = false;		//-------------------------------------------> ADDED (Part 1)
        spouse = null;
        isMarried = false;
    }

    /* Transfer change of the tax allowance from this person to his/her spouse */
    //@ requires isFemale <==> !isMale;
    //@ requires (isFemale && isMarried) ==> (spouse != null && spouse.isMale);
    //@ requires (isMale   && isMarried) ==> (spouse != null && spouse.isFemale);
    //@ requires isMarried ==> (spouse != null && true && spouse.isMarried);
    //@ requires this.isMarried;
    //@ requires (!isMarried && age < 65) ==> tax_allowance == DEFAULT_ALLOWANCE;
    //@ requires (!isMarried && age >= 65) ==> tax_allowance == ALLOWANCE_OAP;
 /*@ requires this.isMarried ==>
   @		   ((tax_allowance + spouse.tax_allowance == 2 * DEFAULT_ALLOWANCE <==> (age < 65  && spouse.age < 65))  ||
   @			(tax_allowance + spouse.tax_allowance == 2 * ALLOWANCE_OAP	 <==> (age >= 65 && spouse.age >= 65)) ||
   @			(tax_allowance + spouse.tax_allowance == DEFAULT_ALLOWANCE + ALLOWANCE_OAP));
   @*/
    //@ ensures isFemale <==> !isMale;
    //@ ensures (isFemale && isMarried) ==> (spouse != null && spouse.isMale);
    //@ ensures (isMale   && isMarried) ==> (spouse != null && spouse.isFemale);
    //@ ensures isMarried ==> (spouse != null && true && spouse.isMarried);
    //@ ensures (!isMarried && age < 65) ==> tax_allowance == DEFAULT_ALLOWANCE;
    //@ ensures (!isMarried && age >= 65) ==> tax_allowance == ALLOWANCE_OAP;
 /*@ ensures this.isMarried ==>
   @		   ((tax_allowance + spouse.tax_allowance == 2 * DEFAULT_ALLOWANCE <==> (age < 65  && spouse.age < 65))  ||
   @			(tax_allowance + spouse.tax_allowance == 2 * ALLOWANCE_OAP	 <==> (age >= 65 && spouse.age >= 65)) ||
   @			(tax_allowance + spouse.tax_allowance == DEFAULT_ALLOWANCE + ALLOWANCE_OAP));
   @*/
    void transferAllowance(int change) {
        tax_allowance = tax_allowance - change;
        spouse.tax_allowance = spouse.tax_allowance + change;
    }

    /* Taxpayer has a birthday and the age increases by one */
    //@ requires age < Integer.MAX_VALUE;
    //@ requires isMarried ==> (spouse != null && spouse.age < Integer.MAX_VALUE);
    //@ requires isFemale <==> !isMale;
    //@ requires (isFemale && isMarried) ==> (spouse != null && spouse.isMale);
    //@ requires (isMale   && isMarried) ==> (spouse != null && spouse.isFemale);
    //@ requires isMarried ==> (spouse != null && true && spouse.isMarried);
 /*@ requires !isMarried ==>
   @		  (tax_allowance == DEFAULT_ALLOWANCE || tax_allowance == ALLOWANCE_OAP);
   @*/
 /*@ requires isMarried ==>
   @		  (tax_allowance == 0 || tax_allowance == DEFAULT_ALLOWANCE ||
   @		   tax_allowance == ALLOWANCE_OAP || tax_allowance == 2 * DEFAULT_ALLOWANCE ||
   @		   tax_allowance == 2 * ALLOWANCE_OAP || tax_allowance == DEFAULT_ALLOWANCE + ALLOWANCE_OAP);
  */
 /*@ requires isMarried ==>
   @		  (spouse.tax_allowance == 0 || spouse.tax_allowance == DEFAULT_ALLOWANCE ||
   @		   spouse.tax_allowance == ALLOWANCE_OAP || spouse.tax_allowance == 2 * DEFAULT_ALLOWANCE ||
   @		   spouse.tax_allowance == 2 * ALLOWANCE_OAP || spouse.tax_allowance == DEFAULT_ALLOWANCE + ALLOWANCE_OAP);
   @*/
    //@ requires (!isMarried && age < 65) ==> tax_allowance == DEFAULT_ALLOWANCE;
    //@ requires (!isMarried && age >= 65) ==> tax_allowance == ALLOWANCE_OAP;
 /*@ requires this.isMarried ==>
   @		   ((tax_allowance + spouse.tax_allowance == 2 * DEFAULT_ALLOWANCE <==> (age < 65  && spouse.age < 65))  ||
   @			(tax_allowance + spouse.tax_allowance == 2 * ALLOWANCE_OAP	 <==> (age >= 65 && spouse.age >= 65)) ||
   @			(tax_allowance + spouse.tax_allowance == DEFAULT_ALLOWANCE + ALLOWANCE_OAP));
   @*/
    //@ ensures isFemale <==> !isMale;
    //@ ensures (isFemale && isMarried) ==> (spouse != null && spouse.isMale);
    //@ ensures (isMale   && isMarried) ==> (spouse != null && spouse.isFemale);
    //@ ensures isMarried ==> (spouse != null && true && spouse.isMarried);
    //@ ensures (!isMarried && age < 65) ==> tax_allowance == DEFAULT_ALLOWANCE;
    //@ ensures (!isMarried && age >= 65) ==> tax_allowance == ALLOWANCE_OAP;
 /*@ ensures this.isMarried ==>
   @		   ((tax_allowance + spouse.tax_allowance == 2 * DEFAULT_ALLOWANCE <==> (age < 65  && spouse.age < 65))  ||
   @			(tax_allowance + spouse.tax_allowance == 2 * ALLOWANCE_OAP	 <==> (age >= 65 && spouse.age >= 65)) ||
   @			(tax_allowance + spouse.tax_allowance == DEFAULT_ALLOWANCE + ALLOWANCE_OAP));
   @*/
    void haveBirthday() {
        age++;

        //Below: ADDED (Part 3)
        if (this.age == 65) {
            if (this.isMarried && this.spouse != null) {
                if (this.tax_allowance == 0) {
                    this.spouse.tax_allowance = this.spouse.tax_allowance + (ALLOWANCE_OAP - DEFAULT_ALLOWANCE);
                } else if (this.spouse.tax_allowance == 0) {
                    this.tax_allowance = this.tax_allowance + (ALLOWANCE_OAP - DEFAULT_ALLOWANCE);
                } else {
                    this.tax_allowance = ALLOWANCE_OAP;
                }
            } else {
                this.tax_allowance = ALLOWANCE_OAP;
            }
        }
    }

}