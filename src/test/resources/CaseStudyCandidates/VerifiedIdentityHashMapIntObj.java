/*
 * Copyright (c) 2000, 2011, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

import java.io.*;

public class VerifiedIdentityHashMapIntObj {

    public static class IntObject {
        public final int hash;

        public IntObject(int hash) {
            this.hash = hash;
        }
    }

    //@ public ghost boolean initialised;

    /*+KEY@ // JML specifically for KeY
      @ public invariant
      @   table != null &&
      @   MINIMUM_CAPACITY == 4 &&
      @   MAXIMUM_CAPACITY == 536870912 &&
      @   MINIMUM_CAPACITY * 2 <= table.length  &&
      @   MAXIMUM_CAPACITY * 2 >= table.length;
      @
      @ // For all key-value pairs: if key == null, then value == null
      @ public invariant
      @   (\forall int i;
      @         0 <= i && i < table.length / 2;
      @         (table[i * 2] == null ==> table[i * 2 + 1] == null));
      @
      @ // Non-empty keys are unique
      @ public invariant
      @   (\forall int i; 0 <= i && i < table.length / 2;
      @       (\forall int j;
      @       i <= j && j < table.length / 2;
      @       (table[2*i] != null && table[2*i] == table[2*j]) ==> i == j));
      @
      @ public invariant
      @   threshold < MAXIMUM_CAPACITY;
      @
      @ // Size equals the number of non-empty keys in the table
      @ public invariant
      @   size == (\num_of int i;
      @       0 <= i < table.length / 2;
      @       table[2*i] != null);
      @
      @ // Table length is a power of two
      @ public invariant
      @   (\exists int i;
      @       0 <= i < table.length;
      @       \dl_pow(2,i) == table.length);
      @
      @ // Table must have at least one empty key-element to prevent
      @ // get-method from endlessly looping when a key is not present.
      @ public invariant
      @   (\exists int i;
      @       0 <= i < table.length / 2;
      @       table[2*i] == null);
      @
      @ // There are no gaps between a key's hashed index and its actual
      @ // index (if the key is at a higher index than the hash code)
      @ public invariant
      @   (\forall int i;
      @       0 <= i < table.length / 2;
      @       table[2*i] != null && 2*i > hash(table[2*i], table.length) ==>
      @       (\forall int j;
      @           hash(table[2*i], table.length) / 2 <= j < i;
      @           table[2*j] != null));
      @
      @ // There are no gaps between a key's hashed index and its actual
      @ // index (if the key is at a lower index than the hash code)
      @ public invariant
      @   (\forall int i;
      @       0 <= i < table.length / 2;
      @       table[2*i] != null && 2*i < hash(table[2*i], table.length) ==>
      @       (\forall int j;
      @           hash(table[2*i], table.length) <= 2*j < table.length || 0 <= 2*j < 2*i;
      @           table[2*j] != null));
      @*/
    /*+OPENJML@ // JML for non-KeY tools, i.e. JJBMC
      @ public invariant
      @   table != null &&
      @   MINIMUM_CAPACITY == 4 &&
      @   DEFAULT_CAPACITY == 4 &&
      @   MAXIMUM_CAPACITY == 8 &&
      @   MINIMUM_CAPACITY * 2 <= table.length  &&
      @   MAXIMUM_CAPACITY * 2 >= table.length;
      @
      @ // For all key-value pairs: if key == null, then value == null
      @ public invariant
      @   (\forall int i;
      @         0 <= i && i < table.length / 2;
      @         (table[i * 2] == null ==> table[i * 2 + 1] == null));
      @
      @ // Non-empty keys are unique
      @ public invariant
      @ (\forall int i; 0 <= i && i < table.length / 2;
      @     (\forall int j;
      @     i <= j && j < table.length / 2;
      @     (table[2*i] != null && table[2*i] == table[2*j]) ==> i == j));
      @
      @ public invariant
      @   threshold < MAXIMUM_CAPACITY;
      @
      @ // Table length is a power of two
      @ public invariant
      @   (table.length & (table.length - 1)) == 0;
      @
      @ // Table must have at least one empty key-element to prevent
      @ // get-method from endlessly looping when a key is not present.
      @ public invariant
      @   (\exists int i;
      @       0 <= i < table.length / 2;
      @       table[2*i] == null);
      @
      @ // There are no gaps between a key's hashed index and its actual
      @ // index (if the key is at a higher index than the hash code)
      @ public invariant
      @   (\forall int i;
      @       0 <= i < table.length / 2;
      @       table[2*i] != null && 2*i > hash(table[2*i], table.length) ==>
      @       (\forall int j;
      @           hash(table[2*i], table.length) / 2 <= j < i;
      @           table[2*j] != null));
      @
      @ // There are no gaps between a key's hashed index and its actual
      @ // index (if the key is at a lower index than the hash code)
      @ public invariant
      @   (\forall int i;
      @       0 <= i < table.length / 2;
      @       table[2*i] != null && 2*i < hash(table[2*i], table.length) ==>
      @       (\forall int j;
      @           hash(table[2*i], table.length) / 2 <= j < table.length / 2;
      @           table[2*j] != null));
      @
      @ public invariant
      @   (\forall int i;
      @       0 <= i < table.length / 2;
      @       table[2*i] != null && 2*i < hash(table[2*i], table.length) ==>
      @       (\forall int j;
      @           0 <= j < hash(table[2*i], table.length) / 2;
      @           table[2*j] != null));
      @
      @
      @*/

    public int count(IntObject[] table) {
        int res = 0;
        for(int i = 0; i < table.length; ++i) {
            res += table[i] == null ? 0 : 1;
        }
        return res;
    }

    /**
     * The initial capacity used by the no-args constructor.
     * MUST be a power of two.  The value 32 corresponds to the
     * (specified) expected maximum size of 21, given a load factor
     * of 2/3.
     */
    //public /*@  @*/ static final int DEFAULT_CAPACITY =  32; // Original code. Disable for JJBMC
    public /*@  @*/ static final int DEFAULT_CAPACITY =  4; // Enable for JJBMC

    /**
     * The minimum capacity, used if a lower value is implicitly specified
     * by either of the constructors with arguments.  The value 4 corresponds
     * to an expected maximum size of 2, given a load factor of 2/3.
     * MUST be a power of two.
     */
    public /*@  @*/ static final int MINIMUM_CAPACITY =  4;

    /**
     * The maximum capacity, used if a higher value is implicitly specified
     * by either of the constructors with arguments.
     * MUST be a power of two <= 1<<29.
     */
    //public /*@  @*/ static final int MAXIMUM_CAPACITY =  1 << 29; // Original code. Disable for JJBMC
    public /*@  @*/ static final int MAXIMUM_CAPACITY =  8; // Enable for JJBMC

    /**
     * The table, resized as necessary. Length MUST always be a power of two.
     */
    public /*@  @*/ transient IntObject[] table;

    /**
     * The number of key-value mappings contained in this identity hash map.
     *
     * @serial
     */
    public /*@  @*/ int size;

    /**
     * The number of modifications, to support fast-fail iterators
     */
    public /*@  @*/ transient int modCount;

    /**
     * The next size value at which to resize (capacity * load factor).
     */
    public /*@  @*/ transient int threshold;

    /**
     * Value representing null keys inside tables.
     */
    public /*@  @*/ static final IntObject NULL_KEY = new IntObject(0);

    /**
     * Use NULL_KEY for key if it is null.
     */
    /*@ public normal_behavior
      @   ensures key == null ==> \result == NULL_KEY;
      @   ensures key != null ==> \result == key;
      @*/
    public static /*@ pure @*/ IntObject maskNull(IntObject key) {
        return (key == null ? NULL_KEY : key);
    }

    /**
     * Returns internal representation of null key back to caller as null.
     */
    /*@ public normal_behavior
      @   ensures key == NULL_KEY ==> \result == null;
      @   ensures key != NULL_KEY ==> \result == key;
      @*/
    public /*@  @*/ static /*@ pure nullable @*/ IntObject unmaskNull(IntObject key) {
        return (key == NULL_KEY ? null : key);
    }

    /**
     * Constructs a new, empty identity hash map with a default expected
     * maximum size (21).
     */
    /*@ public normal_behavior
      @   ensures
      @     DEFAULT_CAPACITY == 4 &&
      @     table.length == 2 * DEFAULT_CAPACITY &&
      @     size == 0;
      @*/
    public /*@ pure @*/ VerifiedIdentityHashMapIntObj() {
        init(DEFAULT_CAPACITY);
    }

    /**
     * Constructs a new, empty map with the specified expected maximum size.
     * Putting more than the expected number of key-value mappings into
     * the map may cause the internal data structure to grow, which may be
     * somewhat time-consuming.
     *
     * @param expectedMaxSize the expected maximum size of the map
     * @throws IllegalArgumentException if <tt>expectedMaxSize</tt> is negative
     */
    /*+KEY@
      @ public exceptional_behavior
      @   requires
      @     expectedMaxSize < 0;
      @   signals_only
      @     IllegalArgumentException;
      @   signals
      @     (IllegalArgumentException e) true;
      @   assignable
      @     \nothing;
      @*/
    /*@ public normal_behavior
      @   requires
      @     expectedMaxSize >= 0;
      @   ensures
      @     table.length == 2 * capacity(expectedMaxSize) &&
      @     size == 0;
      @*/
    public /*@ pure @*/ VerifiedIdentityHashMapIntObj(int expectedMaxSize) {
        if (expectedMaxSize < 0)
            throw new IllegalArgumentException("expectedMaxSize is negative: "
                    + expectedMaxSize);
        init(capacity(expectedMaxSize));
    }

    /**
     * Returns the appropriate capacity for the specified expected maximum
     * size.  Returns the smallest power of two between MINIMUM_CAPACITY
     * and MAXIMUM_CAPACITY, inclusive, that is greater than
     * (3 * expectedMaxSize)/2, if such a number exists.  Otherwise
     * returns MAXIMUM_CAPACITY.  If (3 * expectedMaxSize)/2 is negative, it
     * is assumed that overflow has occurred, and MAXIMUM_CAPACITY is returned.
     */
    /*+KEY@
      @ public normal_behavior
      @   requires
      @     MAXIMUM_CAPACITY == 536870912 &&
      @     ((3 * expectedMaxSize) / 2) < 0;
      @   ensures
      @     \result == MAXIMUM_CAPACITY;
      @
      @
      @ public normal_behavior
      @   requires
      @     MAXIMUM_CAPACITY == 536870912 &&
      @     ((3 * expectedMaxSize) / 2) > MAXIMUM_CAPACITY;
      @   ensures
      @     \result == MAXIMUM_CAPACITY;
      @
      @
      @ public normal_behavior
      @   requires
      @     MINIMUM_CAPACITY == 4 &&
      @     MAXIMUM_CAPACITY == 536870912 &&
      @     ((3 * expectedMaxSize) / 2) >= MINIMUM_CAPACITY &&
      @     ((3 * expectedMaxSize) / 2) <= MAXIMUM_CAPACITY;
      @   ensures
      @     \result >= ((3 * expectedMaxSize) / 2) &&
      @     \result < (3 * expectedMaxSize) &&
      @     (\exists int i;
      @       0 <= i < \result;
      @       \dl_pow(2,i) == \result); // result is a power of two
      @
      @
      @ public normal_behavior
      @   requires
      @     MINIMUM_CAPACITY == 4 &&
      @     ((3 * expectedMaxSize) / 2) >= 0 &&
      @     ((3 * expectedMaxSize) / 2) < MINIMUM_CAPACITY;
      @   ensures
      @     \result < MINIMUM_CAPACITY * 2 &&
      @     \result >= MINIMUM_CAPACITY &&
      @     (\exists int i;
      @       0 <= i < \result;
      @       \dl_pow(2,i) == \result); // result is a power of two
      @*/
    /*+OPENJML@
      @ //public normal_behavior
      @ //  requires
      @ //    MAXIMUM_CAPACITY == 4 &&
      @ //    ((3 * expectedMaxSize) / 2) < 0;
      @ //  ensures
      @ //    \result == MAXIMUM_CAPACITY;
      @
      @ //
      @ //public normal_behavior
      @ //  requires
      @ //    MAXIMUM_CAPACITY == 4 &&
      @ //    ((3 * expectedMaxSize) / 2) > MAXIMUM_CAPACITY;
      @ //  ensures
      @ //    \result == MAXIMUM_CAPACITY;
      @
      @ //
      @ public normal_behavior
      @   requires
      @     MINIMUM_CAPACITY == 4 &&
      @     MAXIMUM_CAPACITY == 8 &&
      @     ((3 * expectedMaxSize) / 2) >= MINIMUM_CAPACITY &&
      @     ((3 * expectedMaxSize) / 2) <= MAXIMUM_CAPACITY;
      @   ensures
      @     \result >= ((3 * expectedMaxSize) / 2) &&
      @     \result < (3 * expectedMaxSize) &&
      @     (\result & (\result - 1)) == 0; // result is a power of two
      @
      @ //
      @ //public normal_behavior
      @ //  requires
      @ //    MINIMUM_CAPACITY == 4 &&
      @ //    ((3 * expectedMaxSize) / 2) >= 0 &&
      @ //    ((3 * expectedMaxSize) / 2) < MINIMUM_CAPACITY;
      @ //  ensures
      @ //    \result < MINIMUM_CAPACITY * 2 &&
      @ //    \result >= MINIMUM_CAPACITY &&
      @ //    (\result & (\result - 1)) == 0; // result is a power of two
      @*/
    public /*@ pure @*/ int capacity(int expectedMaxSize)
    // Compute min capacity for expectedMaxSize given a load factor of 2/3
    {
        int minCapacity =  (3 * expectedMaxSize) / 2;

        // Compute the appropriate capacity
        int result;
        if (minCapacity > MAXIMUM_CAPACITY || minCapacity < 0) {
            result = MAXIMUM_CAPACITY;
        } else {
            result = MINIMUM_CAPACITY;
            /*+KEY@
              @ maintaining
              @   result / 2 < minCapacity;
              @ maintaining
              @   (\exists int i;
              @       0 <= i < result;
              @       \dl_pow(2,i) == result); // result is a power of two
              @ decreasing
              @   (minCapacity - result);
              @ assignable
              @   result;
              @*/
            while (result < minCapacity)
                result <<= 1;
        }
        return result;
    }

    /**
     * Initializes object to be an empty map with the specified initial
     * capacity, which is assumed to be a power of two between
     * MINIMUM_CAPACITY and MAXIMUM_CAPACITY inclusive.
     */
    /*+KEY@
      @ public normal_behavior
      @   requires
      @     !initialised &&
      @     MINIMUM_CAPACITY == 4 &&
      @     MAXIMUM_CAPACITY == 536870912 &&
      @     (\exists int i;
      @       0 <= i < initCapacity;
      @       \dl_pow(2,i) == initCapacity) &&
      @     initCapacity >= MINIMUM_CAPACITY &&
      @     initCapacity <= MAXIMUM_CAPACITY &&
      @     size == 0;
      @   assignable
      @     table, threshold;
      @   ensures
      @     initialised &&
      @     threshold == (2 * initCapacity) / 3 &&
      @     table.length == 2 * initCapacity;
      @*/
    /*+OPENJML@
      @ public normal_behavior
      @   requires
      @     !initialised &&
      @     MINIMUM_CAPACITY == 4 &&
      @     MAXIMUM_CAPACITY == 8 &&
      @     (initCapacity & (initCapacity - 1)) == 0 &&
      @     initCapacity >= MINIMUM_CAPACITY &&
      @     initCapacity <= MAXIMUM_CAPACITY &&
      @     size == 0;
      @   assignable
      @     table, threshold;
      @   ensures
      @     initialised &&
      @     threshold == (2 * initCapacity) / 3 &&
      @     table.length == 2 * initCapacity;
      @*/
    public void init(int initCapacity) {
        threshold = (initCapacity * 2) / 3;
        table = new IntObject[2 * initCapacity];

        //@ set initialised = true;
    }

    /**
     * Returns the number of key-value mappings in this identity hash map.
     *
     * @return the number of key-value mappings in this map
     */
    /*@
      @ public normal_behavior
      @   ensures
      @     \result == size;
      @*/
    public /*@ pure @*/ int size() {
        return size;
    }

    /**
     * Returns <tt>true</tt> if this identity hash map contains no key-value
     * mappings.
     *
     * @return <tt>true</tt> if this identity hash map contains no key-value
     *         mappings
     */
    /*@
      @ public normal_behavior
      @   ensures
      @     \result <==> size == 0;
      @*/
    public /*@ pure @*/ boolean isEmpty() {
        return size == 0;
    }

    /**
     * Returns index for IntObject x.
     */
    /*@ public normal_behavior
      @   ensures
      @     (x != null ==> (\result == x.hash &&
      @     \result < length &&
      @     \result > 0)) &&
      @     \result % 2 == 0 &&
      @     (x == null ==> \result == 0);
      @*/
    public static /*@ pure @*/ int hash(IntObject x, int length) {
        if (x == null) {
            return 0;
        }
        int h =  x.hash;
        // Multiply by -127, and left-shift to use least bit as part of hash
        return ((h << 1) - (h << 8)) & (length - 1);
    }

    /**
     * Circularly traverses table of size len.
     */
    /*@ public normal_behavior
      @ ensures
      @ \result == (i + 2 < len ? i + 2 : 0);
      @*/
    public static /*@ pure @*/ int nextKeyIndex(int i, int len) {
        return (i + 2 < len ? i + 2 : 0);
    }

    /**
     * Returns the value to which the specified key is mapped,
     * or {@code null} if this map contains no mapping for the key.
     *
     * <p>More formally, if this map contains a mapping from a key
     * {@code k} to a value {@code v} such that {@code (key == k)},
     * then this method returns {@code v}; otherwise it returns
     * {@code null}.  (There can be at most one such mapping.)
     *
     * <p>A return value of {@code null} does not <i>necessarily</i>
     * indicate that the map contains no mapping for the key; it's
     * possible that the map explicitly maps the key to {@code null}.
     * The {@link #containsKey containsKey} operation may be used to
     * distinguish these two cases.
     *
     * @see #put(IntObject, IntObject)
     */
    /*@
      @ public normal_behavior
      @   ensures
      @     \result != null <==>
      @         (\exists int i;
      @             0 <= i < table.length / 2;
      @             table[i*2] == maskNull(key) && \result == table[i*2 + 1]);
      @   ensures
      @     \result == null <==>
      @         (!(\exists int i;
      @             0 <= i < table.length / 2;
      @             table[i*2] == maskNull(key)) ||
      @         (\exists int i;
      @             0 <= i < table.length / 2;
      @             table[i*2] == maskNull(key) && table[i*2 + 1] == null)
      @         );
      @*/
    public /*@ pure nullable @*/ IntObject get(IntObject key) {
        IntObject k =  maskNull(key);
        IntObject[] tab =  table;
        int len =  tab.length;
        int i =  hash(k, len);
        /*+KEY@
          @ ghost int initialI = i;
          @ decreasing len - (len + i - initialI) % len;
          @ assignable i;
          @*/
        while (true) {
            IntObject item =  tab[i];
            if (item == k)
                return (IntObject) tab[i + 1];
            if (item == null)
                return null;
            i = nextKeyIndex(i, len);
        }
    }

    public int theKeyIndex(IntObject k) {
        int len = table.length;
        int i = hash(maskNull(k), len);
        while(table[i] != null && table[i] != k)
            i = nextKeyIndex(i, len);
        return i;
    }

    /**
     * Tests whether the specified object reference is a key in this identity
     * hash map.
     *
     * @param   key   possible key
     * @return  <code>true</code> if the specified object reference is a key
     *          in this map
     * @see     #containsValue(IntObject)
     */
    /*@
      @ public normal_behavior
      @   ensures
      @     \result <==> (\exists int i;
      @         0 <= i < table.length / 2;
      @         table[i*2] == maskNull(key));
      @*/
    public /*@ pure @*/ boolean containsKey(IntObject key) {
        IntObject k =  maskNull(key);
        IntObject[] tab =  table;
        int len =  tab.length;
        int i =  hash(k, len);
        /*+KEY@
          @ ghost int initialI = i;
          @ decreasing len - (len + i - initialI) % len;
          @ assignable i;
          @*/
        while (true) {
            IntObject item =  tab[i];
            if (item == k)
                return true;
            if (item == null)
                return false;
            i = nextKeyIndex(i, len);
        }
    }

    /**
     * Tests whether the specified object reference is a value in this identity
     * hash map.
     *
     * @param value value whose presence in this map is to be tested
     * @return <tt>true</tt> if this map maps one or more keys to the
     *         specified object reference
     * @see     #containsKey(IntObject)
     */
    /*@
      @ public normal_behavior
      @   ensures
      @     \result <==> (\exists int i;
      @         0 <= i < table.length / 2;
      @         table[i*2] != null && table[i*2 + 1] == value);
      @*/
    public /*@ pure @*/ boolean containsValue(IntObject value) {
        IntObject[] tab =  table;
        /*+KEY@
          @ decreasing tab.length/2 - (i-1)/2;
          @*/
        for (int i =  1; i < tab.length; i += 2)
            if (tab[i] == value && tab[i - 1] != null)
                return true;

        return false;
    }

    /**
     * Tests if the specified key-value mapping is in the map.
     *
     * @param   key   possible key
     * @param   value possible value
     * @return  <code>true</code> if and only if the specified key-value
     *          mapping is in the map
     */
    /*@ public normal_behavior
      @   ensures
      @     \result <==> (\exists int i;
      @         0 <= i < table.length / 2;
      @         table[i*2] == maskNull(key) && table[i*2 + 1] == value);
      @*/
    public /*@  @*/ /*@ pure @*/ boolean containsMapping(IntObject key, IntObject value) {
        IntObject k =  maskNull(key);
        IntObject[] tab =  table;
        int len =  tab.length;
        int i =  hash(k, len);
        /*+KEY@
          @ ghost int initialI = i;
          @ decreasing len - (len + i - initialI) % len;
          @ assignable i;
          @*/
        while (true) {
            IntObject item =  tab[i];
            if (item == k)
                return tab[i + 1] == value;
            if (item == null)
                return false;
            i = nextKeyIndex(i, len);
        }
    }

    /**
     * Associates the specified value with the specified key in this identity
     * hash map.  If the map previously contained a mapping for the key, the
     * old value is replaced.
     *
     * @param key the key with which the specified value is to be associated
     * @param value the value to be associated with the specified key
     * @return the previous value associated with <tt>key</tt>, or
     *         <tt>null</tt> if there was no mapping for <tt>key</tt>.
     *         (A <tt>null</tt> return can  indicate that the map
     *         previously associated <tt>null</tt> with <tt>key</tt>.)
     * @see     IntObject#equals(IntObject)
     * @see     #get(IntObject)
     * @see     #containsKey(IntObject)
     */
    /*+KEY@
      @
      @ public exceptional_behavior
      @   requires
      @     MAXIMUM_CAPACITY == 536870912 &&
      @     size + 1 >= threshold &&
      @     table.length == 2 * MAXIMUM_CAPACITY &&
      @     threshold == MAXIMUM_CAPACITY - 1;
      @   assignable
      @     \nothing;
      @   signals_only
      @     IllegalStateException;
      @   signals
      @     (IllegalStateException e) true;
      @
      @
      @ public normal_behavior
      @   assignable
      @     size, table, table[*], threshold, modCount;
      @   ensures
      @     // If the key already exists, size must not change, modCount must not change,
      @     // and the old value associated with the key is returned
      @     ((\exists int i;
      @         0 <= i < \old(table.length) / 2;
      @         \old(table[i*2]) == maskNull(key))
      @         ==> size == \old(size) && modCount == \old(modCount) &&
      @         (\forall int j;
      @             0 <= j < \old(table.length) - 1 ;
      @             j % 2 == 0 ==> (\old(table[j]) == maskNull(key) ==> \result == \old(table[j + 1])))) &&
      @
      @     // If the key does not exist, size must me increased by 1, modCount must change,
      @     // and null must be returned
      @     (!(\exists int i;
      @         0 <= i < \old(table.length) - 1;
      @         i % 2 == 0 && \old(table[i]) == maskNull(key))
      @         ==> (size == \old(size) + 1) && modCount != \old(modCount) && \result == null) &&
      @
      @     // After execution, all old keys are still present
      @     (\forall int i;
      @         0 <= i < \old(table.length);
      @         i % 2 == 0 ==>
      @         (\exists int j;
      @             0 <= j < table.length;
      @             j % 2 == 0 && \old(table[i]) == table[j])) &&
      @
      @     // After execution, all old values are still present, unless the old value was
      @     // associated with key
      @     (\forall int i;
      @         0 < i < \old(table.length) ;
      @         i % 2 == 1 ==>
      @         \old(table[i-1]) != maskNull(key) ==>
      @             (\exists int j;
      @                 0 < j < table.length;
      @                 j % 2 == 1 && \old(table[i]) == table[j])) &&
      @
      @     // After execution, the table contains the new key associated with the new value
      @     (\exists int i;
      @         0 <= i < table.length - 1 ;
      @         i % 2 == 0 && table[i] == maskNull(key) && table[i + 1] == value);
      @*/
    /*+OPENJML@
      @
      @ public normal_behavior
      @   assignable
      @     size, table, table[*], threshold, modCount;
      @  // this is for JJBMC only. requiering that size is a reasonalbe value and that at least 2 entries are still free
      @   requires 0 <= size && size < table.length &&
      @             (\exists int i; 0 <= i < table.length/2;
      @             (\exists int j; i <= j < table.length/2; i != j && table[i*2] == null && table[j*2] == null));
      @   ensures
      @     // If the key already exists, size must not change, modCount must not change,
      @     // and the old value associated with the key is returned
      @     ((\exists int i;
      @         0 <= i < \old(table.length) / 2;
      @         \old(table[i*2]) == maskNull(key))
      @         ==> size == \old(size) && modCount == \old(modCount) &&
      @         (\forall int j;
      @             0 <= j < \old(table.length) - 1;
      @             j % 2 == 0 ==> (\old(table[j]) == maskNull(key) ==> \result == \old(table[j + 1])))) &&
      @
      @     // If the key does not exist, size must me increased by 1, modCount must change,
      @     // and null must be returned
      @     (!(\exists int i;
      @         0 <= i < \old(table.length) - 1;
      @         i % 2 == 0 && \old(table[i]) == maskNull(key))
      @         ==> (size == \old(size) + 1) && modCount != \old(modCount) && \result == null) &&
      @
      @     // After execution, all old keys are still present
      @     (\forall int i;
      @         0 <= i < \old(table.length);
      @         i % 2 == 0 ==>
      @         (\exists int j;
      @             0 <= j < table.length;
      @             j % 2 == 0 && \old(table[i]) == table[j])) &&
      @
      @     // After execution, all old values are still present, unless the old value was
      @     // associated with key
      @     (\forall int i;
      @         0 < i < \old(table.length) ;
      @         i % 2 == 1 ==>
      @         \old(table[i-1]) != maskNull(key) ==>
      @             (\exists int j;
      @                 0 < j < table.length;
      @                 j % 2 == 1 && \old(table[i]) == table[j])) &&
      @
      @     // After execution, the table contains the new key associated with the new value
      @     (\exists int i;
      @         0 <= i < table.length / 2;
      @         table[i*2] == maskNull(key) && table[i*2 + 1] == value);
      @*/
    public /*@ nullable @*/ IntObject put(IntObject key, IntObject value) {
        IntObject k =  maskNull(key);
        IntObject[] tab =  table;
        int len =  tab.length;
        int i =  hash(k, len);

        IntObject item;
        /*+KEY@
          @ ghost int initialI = i;
          @ decreasing len - (len + i - initialI) % len;
          @ assignable item, i, tab[*];
          @*/
        while ( (item = tab[i]) != null) {
            if (item == k) {
                IntObject oldValue =  (IntObject) tab[i + 1];
                tab[i + 1] = value;
                return oldValue;
            }
            i = nextKeyIndex(i, len);
        }

        /*+KEY@
          @ ensures modCount != \old(modCount);
          @ ensures \dl_inInt(modCount);  // perhaps needed
          @ assignable modCount;
          @*/
        {
            modCount++;
        }
        tab[i] = k;
        tab[i + 1] = value;
        size++;
        //if (++size >= threshold)
            //resize(len); // len == 2 * current capacity.
        return null;
    }

    /**
     * Resize the table to hold given capacity.
     *
     * @param newCapacity the new capacity, must be a power of two.
     */
    /*+KEY@
      @ public exceptional_behavior
      @   requires
      @     MAXIMUM_CAPACITY == 536870912 &&
      @     table.length == 2 * MAXIMUM_CAPACITY &&
      @     threshold == MAXIMUM_CAPACITY - 1;
      @   assignable
      @     \nothing;
      @   signals_only
      @     IllegalStateException;
      @   signals
      @     (IllegalStateException e) true;
      @
      @ public normal_behavior
      @   requires
      @     MAXIMUM_CAPACITY == 536870912 &&
      @     (\exists int i;
      @       0 <= i < newCapacity;
      @       \dl_pow(2,i) == newCapacity) &&
      @     table.length < 2 * MAXIMUM_CAPACITY &&
      @     threshold < MAXIMUM_CAPACITY - 1;
      @   assignable
      @     threshold, table, table[*];
      @   ensures
      @     \old(table.length) == 2 * MAXIMUM_CAPACITY ==>
      @       (threshold == MAXIMUM_CAPACITY - 1 && table.length == \old(table.length)) &&
      @     (\old(table.length) != 2 * MAXIMUM_CAPACITY && \old(table.length) >= (newCapacity * 2)) ==>
      @       table.length == \old(table.length) &&
      @     (\old(table.length) != 2 * MAXIMUM_CAPACITY && \old(table.length) < (newCapacity * 2)) ==>
      @       table.length == (newCapacity * 2);
      @   ensures
      @     // After execution, all old entries are still present
      @     (\forall int i;
      @         0 <= i < \old(table.length) ;
      @         i % 2 == 0 ==>
      @         (\exists int j;
      @             0 <= j < table.length;
      @             j % 2 == 0 ==> (\old(table[i]) == table[j] && \old(table[i+1]) == table[j+1])));
      @*/
    /*+OPENJML@
      @ public normal_behavior
      @   requires
      @     (newCapacity & (newCapacity - 1)) == 0 &&
      @     table.length < 2 * MAXIMUM_CAPACITY &&
      @     threshold < MAXIMUM_CAPACITY - 1;
      @   assignable
      @     threshold, table, table[*];
      @   ensures
      @     \old(table.length) == 2 * MAXIMUM_CAPACITY ==>
      @       (threshold == MAXIMUM_CAPACITY - 1 && table.length == \old(table.length)) &&
      @     (\old(table.length) != 2 * MAXIMUM_CAPACITY && \old(table.length) >= (newCapacity * 2)) ==>
      @       table.length == \old(table.length) &&
      @     (\old(table.length) != 2 * MAXIMUM_CAPACITY && \old(table.length) < (newCapacity * 2)) ==>
      @       table.length == (newCapacity * 2);
      @   ensures
      @     // After execution, all old entries are still present
      @     (\forall int i;
      @         0 <= i < \old(table.length) / 2;
      @         (\exists int j;
      @             0 <= j < table.length / 2;
      @             \old(table[i*2]) == table[j*2] && \old(table[i*2+1]) == table[j*2+1]));
      @*/
    public void resize(int newCapacity)
    // assert (newCapacity & -newCapacity) == newCapacity; // power of 2
    {
        int newLength =  newCapacity * 2;

        IntObject[] oldTable =  table;
        int oldLength =  oldTable.length;
        if (oldLength == 2 * MAXIMUM_CAPACITY) { // can't expand any further
            if (threshold == MAXIMUM_CAPACITY - 1)
                throw new IllegalStateException("Capacity exhausted.");
            threshold = MAXIMUM_CAPACITY - 1;  // Gigantic map!
            return;
        }
        if (oldLength >= newLength)
            return;

        IntObject[] newTable =  new IntObject[newLength];
        threshold = newLength / 3;

        for (int j =  0; j < oldLength; j += 2) {
            IntObject key =  oldTable[j];
            if (key != null) {
                IntObject value =  oldTable[j + 1];
                oldTable[j] = null;
                oldTable[j + 1] = null;
                int i =  hash(key, newLength);
                while (newTable[i] != null)
                    i = nextKeyIndex(i, newLength);
                newTable[i] = key;
                newTable[i + 1] = value;
            }
        }
        table = newTable;
    }

    /**
     * Removes the mapping for this key from this map if present.
     *
     * @param key key whose mapping is to be removed from the map
     * @return the previous value associated with <tt>key</tt>, or
     *         <tt>null</tt> if there was no mapping for <tt>key</tt>.
     *         (A <tt>null</tt> return can  indicate that the map
     *         previously associated <tt>null</tt> with <tt>key</tt>.)
     */
    /*+KEY@
      @
      @ public normal_behavior
      @   requires
      @     // key does not exist in old table?
      @     (\forall int i;
      @        0 <= i < table.length / 2;
      @        table[i*2] != maskNull(key));
      @   assignable
      @     \nothing;
      @   ensures
      @     \result == null &&
      @     table.length == \old(table.length);
      @*/
    /*@
      @ public normal_behavior
      @   requires
      @     // key exists in old table?
      @     (\exists int i;
      @        0 <= i < table.length / 2;
      @        table[i*2] != null &&
      @        table[i*2].hash == maskNull(key).hash);
      @   requires
      @     // there are no two keys with identical hashes
      @     (\forall int i;
      @         0 <= i < table.length / 2;
      @             (\forall int j;
      @                 0 <= j < table.length / 2;
      @                     (table[i*2] != null && table[j*2] != null) ==>
      @                     (hash(table[i*2], table.length) == hash(table[j*2], table.length) ==> i == j)));
      @   assignable
      @     size, table, table[*], modCount;
      @   //ensures
      @     // Size is subtracted by 1
      @   //  size == \old(size) - 1; //todo with new invariant and count
      @
      @   //ensures
      @     // modCount is changed
      @     //modCount != \old(modCount);
      @
      @   ensures
      @     // Result is the removed value
      @     (\exists int j;
      @       0 <= j < \old(table.length) / 2;
      @       (\old(table[j * 2]) != null &&
      @       ((\old(table[j*2]).hash == maskNull(key).hash) && \result == \old(table[j*2 + 1]))));
      @
      @   ensures
      @     // All not-to-be-removed elements are still present
      @     (\forall int i;
      @       0 <= i < \old(table.length) / 2;
      @       \old(table[i * 2]) != null ==>
      @       (\old(table[i * 2]).hash != maskNull(key).hash ==>
      @         (\exists int j;
      @            0 <= j < table.length / 2;
      @            table[j*2] == \old(table[i * 2]) && table[j*2+1] == \old(table[i * 2+1]))));
      @
      @   ensures
      @     // The deleted key no longer exists in the table
      @     !(\exists int i;
      @        0 <= i < table.length / 2;
      @        table[i * 2] != null &&
      @        table[i*2].hash == maskNull(key).hash);
      @*/
    public /*@ nullable @*/ IntObject remove(IntObject key) {
        IntObject k =  maskNull(key);
        Object[] tab =  table;
        int len =  tab.length;
        int i =  hash(k, len);


        /*+KEY@
          @ ghost int initialI = i;
          @ decreasing len - (len + i - initialI) % len;
          @ assignable i, modCount, size, tab[*];
          @*/
        while (true) {
            IntObject item =  table[i];
            if (item.hash == k.hash) {
                modCount++;
                size--;
                IntObject oldValue =  (IntObject) table[i + 1];
                table[i + 1] = null;
                table[i] = null;
                closeDeletion(i);
                return oldValue;
            }
            if (item == null)
                return null;
            i = nextKeyIndex(i, len);
        }
    }

    /**
     * Removes the specified key-value mapping from the map if it is present.
     *
     * @param   key   possible key
     * @param   value possible value
     * @return  <code>true</code> if and only if the specified key-value
     *          mapping was in the map
     */
    /*@
      @ public normal_behavior
      @   requires
      @     // The element exists in the table
      @     ((\exists int i;
      @         0 <= i < table.length / 2;
      @         table[i * 2] == maskNull(key) && table[i * 2 + 1] == value));
      @   assignable
      @     size, table, table[*], modCount;
      @   ensures
      @     size == \old(size) - 1 && modCount != \old(modCount) && \result == true &&
      @
      @     // The to-be-removed element is no longer present
      @     !((\exists int i;
      @         0 <= i < \old(table.length) / 2;
      @         table[i * 2] == maskNull(key) && table[i * 2 + 1] == value)) &&
      @
      @     // All not-to-be-removed elements are still present
      @     (\forall int i;
      @       0 <= i < \old(table.length) / 2;
      @       \old(table[i*2]) != maskNull(key) || \old(table[i*2+1]) != value ==>
      @         (\exists int j;
      @            0 <= j < table.length / 2;
      @            table[j*2] == \old(table[i*2]) && table[j*2+1] == \old(table[i*2+1])));
      @
      @ public normal_behavior
      @   requires
      @     // The element does not exist in the table
      @     !((\exists int i;
      @         0 <= i < table.length / 2;
      @         table[i * 2] == maskNull(key) && table[i * 2 + 1] == value));
      @   assignable
      @     \nothing;
      @   ensures
      @     \result == false &&
      @
      @     // All elements are still present
      @     (\forall int i;
      @       0 <= i < \old(table.length) / 2;
      @       (\exists int j;
      @          0 <= j < table.length / 2;
      @          table[j * 2] == \old(table[i * 2]) && table[j * 2+1] == \old(table[i * 2+1])));
      @*/
    public boolean removeMapping(IntObject key, IntObject value) {
        IntObject k =  maskNull(key);
        IntObject[] tab =  table;
        int len =  tab.length;
        int i =  hash(k, len);

        /*+KEY@
          @ ghost int initialI = i;
          @ decreasing len - (len + i - initialI) % len;
          @ assignable i, modCount, size, tab, table;
          @*/
        while (true) {
            IntObject item =  tab[i];
            if (item == k) {
                if (tab[i + 1] != value)
                    return false;
                modCount++;
                size--;
                tab[i] = null;
                tab[i + 1] = null;
                closeDeletion(i);
                return true;
            }
            if (item == null)
                return false;
            i = nextKeyIndex(i, len);
        }
    }

    /**
     * Rehash all possibly-colliding entries following a
     * deletion. This preserves the linear-probe
     * collision properties required by get, put, etc.
     *
     * @param d the index of a newly empty deleted slot
     */
    /*@
      @ public normal_behavior
      @   assignable table[*];
      @   requires d >= 0 && d < table.length - 1 && d % 2 == 0;
      @   requires table[d] == null && table[d+1] == null;
      @   ensures
      @     size == \old(size) &&
      @     threshold == \old(threshold) &&
      @     table.length == \old(table.length )&&
      @
      @     // All elements are still present
      @     (\forall int i;
      @       0 <= i < \old(table.length) / 2;
      @       (\exists int j;
      @          0 <= j < table.length / 2;
      @          table[j * 2] == \old(table[i * 2]) && table[j * 2 + 1] == \old(table[i * 2 + 1])));
      @
      @     // TODO: finish this contract
      @
      @*/
    public void closeDeletion(int d)
    // Adapted from Knuth Section 6.4 Algorithm R
    {
        IntObject[] tab =  table;
        int len =  tab.length;

        // Look for items to swap into newly vacated slot
        // starting at index immediately following deletion,
        // and continuing until a null slot is seen, indicating
        // the end of a run of possibly-colliding keys.
        IntObject item;
        for (int i =  nextKeyIndex(d, len); tab[i] != null;
             i = nextKeyIndex(i, len))
        // The following test triggers if the item at slot i (which
        // hashes to be at slot r) should take the spot vacated by d.
        // If so, we swap it in, and then continue with d now at the
        // newly vacated i.  This process will terminate when we hit
        // the null slot at the end of this run.
        // The test is messy because we are using a circular table.
        {
            item = tab[i];
            int r =  hash(item, len);
            if ((i < r && (r <= d || d <= i)) || (r <= d && d <= i)) {
                tab[d] = item;
                tab[d + 1] = tab[i + 1];
                tab[i] = null;
                tab[i + 1] = null;
                d = i;
            }
        }
    }

    /**
     * Removes all of the mappings from this map.
     * The map will be empty after this call returns.
     */
    /*@
      @ public normal_behavior
      @   assignable
      @     modCount, size, table, table[*];
      @   ensures
      @     \old(modCount) != modCount &&
      @     \old(table.length) == table.length &&
      @     size == 0 &&
      @     (\forall int i;
      @        0 <= i < table.length;
      @        table[i] == null);
      @*/
    public void clear() {
        modCount++;
        IntObject[] tab =  table;
        /*+KEY@
          @ maintaining
          @   0 <= i && i <= tab.length;
          @ maintaining
          @   (\forall int j; 0 <= j < i; tab[j] == null);
          @ decreasing
          @   tab.length - i;
          @ assignable
          @   \nothing;
          @*/
        for (int i =  0; i < tab.length; i++)
            tab[i] = null;
        size = 0;
    }

    /**
     * Compares the specified object with this map for equality.  Returns
     * <tt>true</tt> if the given object is  a map and the two maps
     * represent identical object-reference mappings.  More formally, this
     * map is equal to another map <tt>m</tt> if and only if
     * <tt>this.entrySet().equals(m.entrySet())</tt>.
     *
     * <p><b>Owing to the reference-equality-based semantics of this map it is
     * possible that the symmetry and transitivity requirements of the
     * <tt>Object.equals</tt> contract may be violated if this map is compared
     * to a normal map.  However, the <tt>Object.equals</tt> contract is
     * guaranteed to hold among <tt>VerifiedIdentityHashMapInt</tt> instances.</b>
     *
     * @param  o object to be compared for equality with this map
     * @return <tt>true</tt> if the specified object is equal to this map
     * @see IntObject#equals(IntObject)
     */
    /*@ also
      @ public normal_behavior
      @   ensures
      @     true;
      @
      @   // TODO: finish this contract
      @*/
    public /*@ pure @*/ boolean equals(Object o) {
        if (o == this) {
            return true;
        } else if (o instanceof VerifiedIdentityHashMapIntObj) {
            VerifiedIdentityHashMapIntObj m =  (VerifiedIdentityHashMapIntObj) o;
            if (m.size() != size)
                return false;

            IntObject[] tab =  m.table;
            for (int i =  0; i < tab.length; i += 2) {
                IntObject k =  tab[i];
                if (k != null && !containsMapping(k, tab[i + 1]))
                    return false;
            }
            return true;
        } else {
            return false;  // o is not a Map
        }
    } // skipped

    /**
     * Returns the hash code value for this map.  The hash code of a map is
     * defined to be the sum of the hash codes of each entry in the map's
     * <tt>entrySet()</tt> view.  This ensures that <tt>m1.equals(m2)</tt>
     * implies that <tt>m1.hashCode()==m2.hashCode()</tt> for any two
     * <tt>VerifiedIdentityHashMap</tt> instances <tt>m1</tt> and <tt>m2</tt>, as
     * required by the general contract of {@link IntObject#hashCode}.
     *
     * <p><b>Owing to the reference-equality-based semantics of the
     * <tt>Map.Entry</tt> instances in the set returned by this map's
     * <tt>entrySet</tt> method, it is possible that the contractual
     * requirement of <tt>Object.hashCode</tt> mentioned in the previous
     * paragraph will be violated if one of the two objects being compared is
     * an <tt>VerifiedIdentityHashMap</tt> instance and the other is a normal map.</b>
     *
     * @return the hash code value for this map
     * @see IntObject#equals(IntObject)
     * @see #equals(IntObject)
     */
    /*@ also
      @ public normal_behavior
      @   ensures
      @     true;
      @
      @   // TODO: finish this contract
      @*/
    public /*@ pure @*/ int hashCode() {
        int result =  0;
        IntObject[] tab =  table;
        for (int i =  0; i < tab.length; i += 2) {
            IntObject key =  tab[i];
            if (key != null) {
                IntObject k =  unmaskNull(key);
                result += System.identityHashCode(k) ^
                        System.identityHashCode(tab[i + 1]);
            }
        }
        return result;
    } // skipped
}