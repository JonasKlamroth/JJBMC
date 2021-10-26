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

package java.util;
import java.io.*;

public class VerifiedIdentityHashMapInt {

    //@ private ghost boolean initialised;

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
      @         (table[i * 2] == 0 ==> table[i * 2 + 1] == 0));
      @
      @ // Non-empty keys are unique
      @ public invariant
      @   (\forall int i; 0 <= i && i < table.length / 2;
      @       (\forall int j;
      @       i <= j && j < table.length / 2;
      @       (table[2*i] != 0 && table[2*i] == table[2*j]) ==> i == j));
      @
      @ public invariant
      @   threshold < MAXIMUM_CAPACITY;
      @
      @ // Size equals the number of non-empty keys in the table
      @ public invariant
      @   size == (\num_of int i;
      @       0 <= i < table.length / 2;
      @       table[2*i] != 0);
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
      @       table[2*i] == 0);
      @
      @ // There are no gaps between a key's hashed index and its actual
      @ // index (if the key is at a higher index than the hash code)
      @ public invariant
      @   (\forall int i;
      @       0 <= i < table.length / 2;
      @       table[2*i] != 0 && 2*i > hash(table[2*i], table.length) ==>
      @       (\forall int j;
      @           hash(table[2*i], table.length) / 2 <= j < i;
      @           table[2*j] != 0));
      @
      @ // There are no gaps between a key's hashed index and its actual
      @ // index (if the key is at a lower index than the hash code)
      @ public invariant
      @   (\forall int i;
      @       0 <= i < table.length / 2;
      @       table[2*i] != 0 && 2*i < hash(table[2*i], table.length) ==>
      @       (\forall int j;
      @           hash(table[2*i], table.length) <= 2*j < table.length || 0 <= 2*j < 2*i;
      @           table[2*j] != 0));
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
      @         (table[i * 2] == 0 ==> table[i * 2 + 1] == 0));
      @
      @ // Non-empty keys are unique
      @ public invariant
      @ (\forall int i; 0 <= i && i < table.length / 2;
      @     (\forall int j;
      @     i <= j && j < table.length / 2;
      @     (table[2*i] != 0 && table[2*i] == table[2*j]) ==> i == j));
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
      @       table[2*i] == 0);
      @
      @ // There are no gaps between a key's hashed index and its actual
      @ // index (if the key is at a higher index than the hash code)
      @ public invariant
      @   (\forall int i;
      @       0 <= i < table.length / 2;
      @       table[2*i] != 0 && 2*i > hash(table[2*i], table.length) ==>
      @       (\forall int j;
      @           hash(table[2*i], table.length) / 2 <= j < i;
      @           table[2*j] != 0));
      @
      @ // There are no gaps between a key's hashed index and its actual
      @ // index (if the key is at a lower index than the hash code)
      @ public invariant
      @   (\forall int i;
      @       0 <= i < table.length / 2;
      @       (table[2*i] != 0 && 2*i < hash(table[2*i], table.length)) ==>
      @       (\forall int j;
      @           0 <= j < i;
      @           table[2*j] != 0));
      @
      @*/

    /**
     * The initial capacity used by the no-args constructor.
     * MUST be a power of two.  The value 32 corresponds to the
     * (specified) expected maximum size of 21, given a load factor
     * of 2/3.
     */
    //private /*@ spec_public @*/ static final int DEFAULT_CAPACITY =  32; // Original code. Disable for JJBMC
    private /*@ spec_public @*/ static final int DEFAULT_CAPACITY =  4; // Enable for JJBMC

    /**
     * The minimum capacity, used if a lower value is implicitly specified
     * by either of the constructors with arguments.  The value 4 corresponds
     * to an expected maximum size of 2, given a load factor of 2/3.
     * MUST be a power of two.
     */
    private /*@ spec_public @*/ static final int MINIMUM_CAPACITY =  4;

    /**
     * The maximum capacity, used if a higher value is implicitly specified
     * by either of the constructors with arguments.
     * MUST be a power of two <= 1<<29.
     */
    //private /*@ spec_public @*/ static final int MAXIMUM_CAPACITY =  1 << 29; // Original code. Disable for JJBMC
    private /*@ spec_public @*/ static final int MAXIMUM_CAPACITY =  8; // Enable for JJBMC

    /**
     * The table, resized as necessary. Length MUST always be a power of two.
     */
    private /*@ spec_public @*/ transient int[] table;

    /**
     * The number of key-value mappings contained in this identity hash map.
     *
     * @serial
     */
    private /*@ spec_public @*/ int size;

    /**
     * The number of modifications, to support fast-fail iterators
     */
    private /*@ spec_public @*/ transient int modCount;

    /**
     * The next size value at which to resize (capacity * load factor).
     */
    private /*@ spec_public @*/ transient int threshold;

    /**
     * Value representing null keys inside tables.
     */
    private /*@ spec_public @*/ static final int NULL_KEY = 0;

    /**
     * Use NULL_KEY for key if it is null.
     */
    /*@ private normal_behavior
      @   ensures key == 0 ==> \result == NULL_KEY;
      @   ensures key != 0 ==> \result == key;
      @*/
    public static /*@ pure @*/ int maskNull(int key) {
        return key;
    }

    /**
     * Returns internal representation of null key back to caller as null.
     */
    /*@ private normal_behavior
      @   ensures key == NULL_KEY ==> \result == 0;
      @   ensures key != NULL_KEY ==> \result == key;
      @*/
    private /*@ spec_public @*/ static /*@ pure nullable @*/ int unmaskNull(int key) {
        return (key == NULL_KEY ? 0 : key);
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
    public /*@ pure @*/ VerifiedIdentityHashMapInt() {
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
      @ private exceptional_behavior
      @   requires
      @     expectedMaxSize < 0;
      @   signals_only
      @     IllegalArgumentException;
      @   signals
      @     (IllegalArgumentException e) true;
      @   assignable
      @     \nothing;
      @*/
    /*@ private normal_behavior
      @   requires
      @     expectedMaxSize >= 0;
      @   ensures
      @     table.length == 2 * capacity(expectedMaxSize) &&
      @     size == 0;
      @*/
    public /*@ pure @*/ VerifiedIdentityHashMapInt(int expectedMaxSize) {
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
      @ private normal_behavior
      @   requires
      @     MAXIMUM_CAPACITY == 536870912 &&
      @     ((3 * expectedMaxSize) / 2) < 0;
      @   ensures
      @     \result == MAXIMUM_CAPACITY;
      @
      @ 
      @ private normal_behavior
      @   requires
      @     MAXIMUM_CAPACITY == 536870912 &&
      @     ((3 * expectedMaxSize) / 2) > MAXIMUM_CAPACITY;
      @   ensures
      @     \result == MAXIMUM_CAPACITY;
      @
      @ 
      @ private normal_behavior
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
      @ private normal_behavior
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
      @ //private normal_behavior
      @ //  requires
      @ //    MAXIMUM_CAPACITY == 4 &&
      @ //    ((3 * expectedMaxSize) / 2) < 0;
      @ //  ensures
      @ //    \result == MAXIMUM_CAPACITY;
      @
      @ //
      @ //private normal_behavior
      @ //  requires
      @ //    MAXIMUM_CAPACITY == 4 &&
      @ //    ((3 * expectedMaxSize) / 2) > MAXIMUM_CAPACITY;
      @ //  ensures
      @ //    \result == MAXIMUM_CAPACITY;
      @
      @ //
      @ private normal_behavior
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
      @ //private normal_behavior
      @ //  requires
      @ //    MINIMUM_CAPACITY == 4 &&
      @ //    ((3 * expectedMaxSize) / 2) >= 0 &&
      @ //    ((3 * expectedMaxSize) / 2) < MINIMUM_CAPACITY;
      @ //  ensures
      @ //    \result < MINIMUM_CAPACITY * 2 &&
      @ //    \result >= MINIMUM_CAPACITY &&
      @ //    (\result & (\result - 1)) == 0; // result is a power of two
      @*/
    private /*@ pure @*/ int capacity(int expectedMaxSize)
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
      @ private normal_behavior
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
      @ private normal_behavior
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
    private void init(int initCapacity) {
        threshold = (initCapacity * 2) / 3;
        table = new int[2 * initCapacity];

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
     * Returns index for int x.
     */
    /*@ public normal_behavior
      @   ensures
      @     (x != 0 ==> (\result == x &&
      @     \result < length &&
      @     \result > 0)) &&
      @     \result % 2 == 0 &&
      @     (x == 0 ==> \result == 0);
      @*/
    public static /*@ pure @*/ int hash(int x, int length) {
        if(x == 0) {
            return 0;
        }
        int h =  x;
        // Multiply by -127, and left-shift to use least bit as part of hash
        return ((h << 1) - (h << 8)) & (length - 1);
    }

    /**
     * Circularly traverses table of size len.
     */
    /*@ private normal_behavior
      @ ensures
      @ \result == (i + 2 < len ? i + 2 : 0);
      @*/
    private static /*@ pure @*/ int nextKeyIndex(int i, int len) {
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
     * @see #put(int, int)
     */
    /*@ 
      @ public normal_behavior
      @   ensures
      @     \result != 0 <==>
      @         (\exists int i;
      @             0 <= i < table.length / 2;
      @             table[i*2] == maskNull(key) && \result == table[i*2 + 1]);
      @   ensures
      @     \result == 0 <==>
      @         (!(\exists int i;
      @             0 <= i < table.length / 2;
      @             table[i*2] == maskNull(key)) ||
      @         (\exists int i;
      @             0 <= i < table.length / 2;
      @             table[i*2] == maskNull(key) && table[i*2 + 1] == 0)
      @         );
      @*/
    public /*@ pure nullable @*/ int get(int key) {
        int k =  maskNull(key);
        int[] tab =  table;
        int len =  tab.length;
        int i =  hash(k, len);
        /*+KEY@
          @ ghost int initialI = i;
          @ decreasing len - (len + i - initialI) % len;
          @ assignable i;
          @*/
        while (true) {
            int item =  tab[i];
            if (item == k)
                return (int) tab[i + 1];
            if (item == 0)
                return 0;
            i = nextKeyIndex(i, len);
        }
    }

    private int theKeyIndex(int k) {
        int len = table.length;
        int i = hash(maskNull(k), len);
        while(table[i] != 0 && table[i] != k)
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
     * @see     #containsValue(int)
     */
    /*@ 
      @ public normal_behavior
      @   ensures
      @     \result <==> (\exists int i;
      @         0 <= i < table.length / 2;
      @         table[i*2] == maskNull(key));
      @*/
    public /*@ pure @*/ boolean containsKey(int key) {
        int k =  maskNull(key);
        int[] tab =  table;
        int len =  tab.length;
        int i =  hash(k, len);
        /*+KEY@
          @ ghost int initialI = i;
          @ decreasing len - (len + i - initialI) % len;
          @ assignable i;
          @*/
        while (true) {
            int item =  tab[i];
            if (item == k)
                return true;
            if (item == 0)
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
     * @see     #containsKey(int)
     */
    /*@ 
      @ public normal_behavior
      @   ensures
      @     \result <==> (\exists int i;
      @         0 <= i < table.length / 2;
      @         table[i*2] != 0 && table[i*2 + 1] == value);
      @*/
    public /*@ pure @*/ boolean containsValue(int value) {
        int[] tab =  table;
        /*+KEY@
          @ decreasing tab.length/2 - (i-1)/2;
          @*/
        for (int i =  1; i < tab.length; i += 2)
            if (tab[i] == value && tab[i - 1] != 0)
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
    /*@ private normal_behavior
      @   ensures
      @     \result <==> (\exists int i;
      @         0 <= i < table.length / 2;
      @         table[i*2] == maskNull(key) && table[i*2 + 1] == value);
      @*/
    private /*@ spec_public @*/ /*@ pure @*/ boolean containsMapping(int key, int value) {
        int k =  maskNull(key);
        int[] tab =  table;
        int len =  tab.length;
        int i =  hash(k, len);
        /*+KEY@
          @ ghost int initialI = i;
          @ decreasing len - (len + i - initialI) % len;
          @ assignable i;
          @*/
        while (true) {
            int item =  tab[i];
            if (item == k)
                return tab[i + 1] == value;
            if (item == 0)
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
     * @see     int#equals(int)
     * @see     #get(int)
     * @see     #containsKey(int)
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
      @             0 <= j < \old(table.length) - 1 && j % 2 == 0;
      @             \old(table[j]) == maskNull(key) ==> \result == \old(table[j + 1]))) &&
      @
      @     // If the key does not exist, size must me increased by 1, modCount must change,
      @     // and null must be returned
      @     (!(\exists int i;
      @         0 <= i < \old(table.length) - 1;
      @         i % 2 == 0 && \old(table[i]) == maskNull(key))
      @         ==> (size == \old(size) + 1) && modCount != \old(modCount) && \result == 0) &&
      @
      @     // After execution, all old keys are still present
      @     (\forall int i;
      @         0 <= i < \old(table.length) && i % 2 == 0;
      @         (\exists int j;
      @             0 <= j < table.length;
      @             j % 2 == 0 && \old(table[i]) == table[j])) &&
      @
      @     // After execution, all old values are still present, unless the old value was
      @     // associated with key
      @     (\forall int i;
      @         0 < i < \old(table.length) && i % 2 == 1;
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
      @             (\exists int j; i <= j < table.length/2; i != j && table[i*2] == 0 && table[j*2] == 0));
      @   ensures
      @     // If the key already exists, size must not change, modCount must not change,
      @     // and the old value associated with the key is returned
      @     ((\exists int i;
      @         0 <= i < \old(table.length) / 2;
      @         \old(table[i*2]) == maskNull(key))
      @         ==> size == \old(size) && modCount == \old(modCount) &&
      @         (\forall int j;
      @             0 <= j < \old(table.length) - 1 && j % 2 == 0;
      @             \old(table[j]) == maskNull(key) ==> \result == \old(table[j + 1]))) &&
      @
      @     // If the key does not exist, size must me increased by 1, modCount must change,
      @     // and null must be returned
      @     (!(\exists int i;
      @         0 <= i < \old(table.length) - 1;
      @         i % 2 == 0 && \old(table[i]) == maskNull(key))
      @         ==> (size == \old(size) + 1) && modCount != \old(modCount) && \result == 0) &&
      @
      @     // After execution, all old keys are still present
      @     (\forall int i;
      @         0 <= i < \old(table.length) && i % 2 == 0;
      @         (\exists int j;
      @             0 <= j < table.length;
      @             j % 2 == 0 && \old(table[i]) == table[j])) &&
      @
      @     // After execution, all old values are still present, unless the old value was
      @     // associated with key
      @     (\forall int i;
      @         0 < i < \old(table.length) && i % 2 == 1;
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
    public /*@ nullable @*/ int put(int key, int value) {
        int k =  maskNull(key);
        int[] tab =  table;
        int len =  tab.length;
        int i =  hash(k, len);

        int item;
        /*+KEY@
          @ ghost int initialI = i;
          @ decreasing len - (len + i - initialI) % len;
          @ assignable item, i, tab[*];
          @*/
        while ( (item = tab[i]) != 0) {
            if (item == k) {
                int oldValue =  (int) tab[i + 1];
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
        return 0;
    }

    /**
     * Resize the table to hold given capacity.
     *
     * @param newCapacity the new capacity, must be a power of two.
     */
    /*+KEY@
      @ private exceptional_behavior
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
      @ private normal_behavior
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
      @         0 <= i < \old(table.length) && i % 2 == 0;
      @         (\exists int j;
      @             0 <= j < table.length && j % 2 == 0;
      @             \old(table[i]) == table[j] && \old(table[i+1]) == table[j+1]));
      @*/
    /*+OPENJML@
      @ private normal_behavior
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
    private void resize(int newCapacity)
    // assert (newCapacity & -newCapacity) == newCapacity; // power of 2
    {
        int newLength =  newCapacity * 2;

        int[] oldTable =  table;
        int oldLength =  oldTable.length;
        if (oldLength == 2 * MAXIMUM_CAPACITY) { // can't expand any further
            if (threshold == MAXIMUM_CAPACITY - 1)
                throw new IllegalStateException("Capacity exhausted.");
            threshold = MAXIMUM_CAPACITY - 1;  // Gigantic map!
            return;
        }
        if (oldLength >= newLength)
            return;

        int[] newTable =  new int[newLength];
        threshold = newLength / 3;

        for (int j =  0; j < oldLength; j += 2) {
            int key =  oldTable[j];
            if (key != 0) {
                int value =  oldTable[j + 1];
                oldTable[j] = 0;
                oldTable[j + 1] = 0;
                int i =  hash(key, newLength);
                while (newTable[i] != 0)
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
      @     \result == 0 &&
      @     table.length == \old(table.length);
      @*/
    /*@
      @ public normal_behavior
      @   requires
      @     key != 0 &&
      @
      @     // key exists in old table?
      @     (\exists int i;
      @        0 <= i < table.length / 2;
      @        table[i*2] == maskNull(key));
      @   assignable
      @     size, table, table[*], modCount;
      @   ensures
      @     // Size is subtracted by 1
      @     size == \old(size) - 1 &&
      @
      @     // modCount is changed
      @     modCount != \old(modCount) &&
      @
      @     // Result is the removed value
      @     (\forall int j;
      @       0 <= j < \old(table.length) / 2;
      @       \old(table[j*2]) == maskNull(key) ==> \result == \old(table[j*2 + 1])) &&
      @
      @     // All not-to-be-removed elements are still present
      @     (\forall int i;
      @       0 <= i < \old(table.length) / 2;
      @       \old(table[i * 2]) != maskNull(key) ==>
      @         (\exists int j;
      @            0 <= j < table.length / 2;
      @            table[j*2] == \old(table[i * 2]) && table[j*2+1] == \old(table[i * 2+1]))) &&
      @
      @     // The deleted key no longer exists in the table
      @     !(\exists int i;
      @        0 <= i < table.length / 2;
      @        table[i*2] == maskNull(key));
      @*/
    public /*@ nullable @*/ int remove(int key) {
        int k =  maskNull(key);
        int[] tab =  table;
        int len =  tab.length;
        int i = hash(k, len);

        /*+KEY@
          @ ghost int initialI = i;
          @ decreasing len - (len + i - initialI) % len;
          @ assignable i, modCount, size, tab[*];
          @*/
        while (true) {
            int item =  tab[i];
            if (item == k) {
                modCount++;
                size--;
                int oldValue =  (int) tab[i + 1];
                tab[i + 1] = 0;
                tab[i] = 0;
                closeDeletion(i);
                return oldValue;
            }
            if (item == 0)
                return 0;
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
      @ private normal_behavior
      @   requires true;
      @     // The element exists in the table
      @     //((\exists int i;
      @      //   0 <= i < table.length / 2;
      @       //  table[i * 2] == maskNull(key) && table[i * 2 + 1] == value));
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
      @ private normal_behavior
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
    private boolean removeMapping(int key, int value) {
        int k =  maskNull(key);
        int[] tab =  table;
        int len =  tab.length;
        int i =  hash(k, len);

        /*+KEY@
          @ ghost int initialI = i;
          @ decreasing len - (len + i - initialI) % len;
          @ assignable i, modCount, size, tab, table;
          @*/
        while (true) {
            int item =  tab[i];
            if (item == k) {
                if (tab[i + 1] != value)
                    return false;
                modCount++;
                size--;
                tab[i] = 0;
                tab[i + 1] = 0;
                closeDeletion(i);
                return true;
            }
            if (item == 0)
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
      @ private normal_behavior
      @   assignable table[*];
      @   requires d >= 0 && d < table.length - 1 && d % 2 == 0;
      @   requires table[d] == 0 && table[d+1] == 0;
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
    private void closeDeletion(int d)
    // Adapted from Knuth Section 6.4 Algorithm R
    {
        int[] tab =  table;
        int len =  tab.length;

        // Look for items to swap into newly vacated slot
        // starting at index immediately following deletion,
        // and continuing until a null slot is seen, indicating
        // the end of a run of possibly-colliding keys.
        int item;
        for (int i =  nextKeyIndex(d, len); tab[i] != 0;
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
                tab[i] = 0;
                tab[i + 1] = 0;
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
      @        table[i] == 0);
      @*/
    public void clear() {
        modCount++;
        int[] tab =  table;
        /*+KEY@
          @ maintaining
          @   0 <= i && i <= tab.length;
          @ maintaining
          @   (\forall int j; 0 <= j < i; tab[j] == 0);
          @ decreasing
          @   tab.length - i;
          @ assignable
          @   \nothing;
          @*/
        for (int i =  0; i < tab.length; i++)
            tab[i] = 0;
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
     * @see int#equals(int)
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
        } else if (o instanceof VerifiedIdentityHashMapInt) {
            VerifiedIdentityHashMapInt m =  (VerifiedIdentityHashMapInt) o;
            if (m.size() != size)
                return false;

            int[] tab =  m.table;
            for (int i =  0; i < tab.length; i += 2) {
                int k =  tab[i];
                if (k != 0 && !containsMapping(k, tab[i + 1]))
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
     * required by the general contract of {@link int#hashCode}.
     *
     * <p><b>Owing to the reference-equality-based semantics of the
     * <tt>Map.Entry</tt> instances in the set returned by this map's
     * <tt>entrySet</tt> method, it is possible that the contractual
     * requirement of <tt>Object.hashCode</tt> mentioned in the previous
     * paragraph will be violated if one of the two objects being compared is
     * an <tt>VerifiedIdentityHashMap</tt> instance and the other is a normal map.</b>
     *
     * @return the hash code value for this map
     * @see int#equals(int)
     * @see #equals(int)
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
        int[] tab =  table;
        for (int i =  0; i < tab.length; i += 2) {
            int key =  tab[i];
            if (key != 0) {
                int k =  unmaskNull(key);
                result += System.identityHashCode(k) ^
                        System.identityHashCode(tab[i + 1]);
            }
        }
        return result;
    } // skipped
}