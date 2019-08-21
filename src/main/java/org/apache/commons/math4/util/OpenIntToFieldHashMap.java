/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.commons.math4.util;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.Serializable;
import java.lang.reflect.Array;
import java.util.ConcurrentModificationException;
import java.util.NoSuchElementException;

import org.apache.commons.math4.Field;
import org.apache.commons.math4.FieldElement;

import org.checkerframework.checker.index.qual.NonNegative;
import org.checkerframework.checker.index.qual.SameLen;
import org.checkerframework.checker.index.qual.IndexFor;
import org.checkerframework.checker.index.qual.LTLengthOf;

/**
 * Open addressed map from int to FieldElement.
 * <p>This class provides a dedicated map from integers to FieldElements with a
 * much smaller memory overhead than standard <code>java.util.Map</code>.</p>
 * <p>This class is not synchronized. The specialized iterators returned by
 * {@link #iterator()} are fail-fast: they throw a
 * <code>ConcurrentModificationException</code> when they detect the map has been
 * modified during iteration.</p>
 * @param <T> the type of the field elements
 * @since 2.0
 */
public class OpenIntToFieldHashMap<T extends FieldElement<T>> implements Serializable {

    /** Status indicator for free table entries. */
    protected static final byte FREE    = 0;

    /** Status indicator for full table entries. */
    protected static final byte FULL    = 1;

    /** Status indicator for removed table entries. */
    protected static final byte REMOVED = 2;

    /** Serializable version identifier. */
    private static final long serialVersionUID = -9179080286849120720L;

    /** Load factor for the map. */
    private static final float LOAD_FACTOR = 0.5f;

    /** Default starting size.
     * <p>This must be a power of two for bit mask to work properly. </p>
     */
    private static final int DEFAULT_EXPECTED_SIZE = 16;

    /** Multiplier for size growth when map fills up.
     * <p>This must be a power of two for bit mask to work properly. </p>
     */
    private static final int RESIZE_MULTIPLIER = 2;

    /** Number of bits to perturb the index when probing for collision resolution. */
    private static final int PERTURB_SHIFT = 5;

    /** Field to which the elements belong. */
    private final Field<T> field;

    /** Keys table. */
    private int @SameLen({"this.states", "this.values"}) [] keys;

    /** Values table. */
    private T @SameLen({"this.states", "this.keys"}) [] values;

    /** States table. */
    private byte @SameLen({"this.values", "this.keys"}) [] states;

    /** Return value for missing entries. */
    private final T missingEntries;

    /** Current size of the map. */
    private int size;

    /** Bit mask for hash values. */
    private @IndexFor({"this.states", "this.keys","this.values"}) int mask;

    /** Modifications count. */
    private transient int count;

    /**
     * Build an empty map with default size and using zero for missing entries.
     * @param field field to which the elements belong
     */
    public OpenIntToFieldHashMap(final Field<T>field) {
        this(field, DEFAULT_EXPECTED_SIZE, field.getZero());
    }

    /**
     * Build an empty map with default size
     * @param field field to which the elements belong
     * @param missingEntries value to return when a missing entry is fetched
     */
    public OpenIntToFieldHashMap(final Field<T>field, final T missingEntries) {
        this(field,DEFAULT_EXPECTED_SIZE, missingEntries);
    }

    /**
     * Build an empty map with specified size and using zero for missing entries.
     * @param field field to which the elements belong
     * @param expectedSize expected number of elements in the map
     */
    public OpenIntToFieldHashMap(final Field<T> field,final int expectedSize) {
        this(field,expectedSize, field.getZero());
    }

    /**
     * Build an empty map with specified size.
     * @param field field to which the elements belong
     * @param expectedSize expected number of elements in the map
     * @param missingEntries value to return when a missing entry is fetched
     */
    @SuppressWarnings("index:assignment.type.incompatible") // #1: all three are assigned with equal length, i.e., capacity, hence @SameLen
    public OpenIntToFieldHashMap(final Field<T> field,final int expectedSize,
                                  final T missingEntries) {
        this.field = field;
        final int capacity = computeCapacity(expectedSize);
        keys   = new int[capacity]; // #1
        values = buildArray(capacity); // #1
        states = new byte[capacity]; // #1
        this.missingEntries = missingEntries;
        mask   = capacity - 1;
    }

    /**
     * Copy constructor.
     * @param source map to copy
     */
    @SuppressWarnings({"index:assignment.type.incompatible", "index:argument.type.incompatible"}) /*
    #1: all three are assigned with equal length, i.e., capacity, hence @SameLen
    #2: length = source.values.length due to the @SameLen annotation
    */
    public OpenIntToFieldHashMap(final OpenIntToFieldHashMap<T> source) {
        field = source.field;
        final int length = source.keys.length;
        keys = new int[length]; // #1
        System.arraycopy(source.keys, 0, keys, 0, length);
        values = buildArray(length); // #1
        System.arraycopy(source.values, 0, values, 0, length); // #2
        states = new byte[length]; // #1
        System.arraycopy(source.states, 0, states, 0, length);
        missingEntries = source.missingEntries;
        size  = source.size;
        mask  = source.mask;
        count = source.count;
    }

    /**
     * Compute the capacity needed for a given size.
     * @param expectedSize expected size of the map
     * @return capacity to use for the specified size
     */
    @SuppressWarnings({"index:return.type.incompatible","index:argument.type.incompatible"}) // #1: capacity by #0.1 is (int) FastMath.ceil(@NonNegative / @NonNegative) which is @NonNegative
    private static @NonNegative int computeCapacity(final int expectedSize) {
        if (expectedSize == 0) {
            return 1;
        }
        final int capacity   = (int) FastMath.ceil(expectedSize / LOAD_FACTOR); // #0.1
        final int powerOfTwo = Integer.highestOneBit(capacity);
        if (powerOfTwo == capacity) {
            return capacity; // #1
        }
        return nextPowerOfTwo(capacity); // #1
    }

    /**
     * Find the smallest power of two greater than the input value
     * @param i input value
     * @return smallest power of two greater than the input value
     */
    private static int nextPowerOfTwo(final int i) {
        return Integer.highestOneBit(i) << 1;
    }

    /**
     * Get the stored value associated with the given key
     * @param key key associated with the data
     * @return data associated with the key
     */
    public T get(final int key) {

        final int hash  = hashOf(key);
        int index = hash & mask;
        if (containsKey(key, index)) {
            return values[index];
        }

        if (states[index] == FREE) {
            return missingEntries;
        }

        int j = index;
        for (int perturb = perturb(hash); states[index] != FREE; perturb >>= PERTURB_SHIFT) {
            j = probe(perturb, j);
            index = j & mask;
            if (containsKey(key, index)) {
                return values[index];
            }
        }

        return missingEntries;

    }

    /**
     * Check if a value is associated with a key.
     * @param key key to check
     * @return true if a value is associated with key
     */
    public boolean containsKey(final int key) {

        final int hash  = hashOf(key);
        int index = hash & mask;
        if (containsKey(key, index)) {
            return true;
        }

        if (states[index] == FREE) {
            return false;
        }

        int j = index;
        for (int perturb = perturb(hash); states[index] != FREE; perturb >>= PERTURB_SHIFT) {
            j = probe(perturb, j);
            index = j & mask;
            if (containsKey(key, index)) {
                return true;
            }
        }

        return false;

    }

    /**
     * Get an iterator over map elements.
     * <p>The specialized iterators returned are fail-fast: they throw a
     * <code>ConcurrentModificationException</code> when they detect the map
     * has been modified during iteration.</p>
     * @return iterator over the map elements
     */
    public Iterator iterator() {
        return new Iterator();
    }

    /**
     * Perturb the hash for starting probing.
     * @param hash initial hash
     * @return perturbed hash
     */
    private static int perturb(final int hash) {
        return hash & 0x7fffffff;
    }

    /**
     * Find the index at which a key should be inserted
     * @param key key to lookup
     * @return index at which key should be inserted
     */
    private int findInsertionIndex(final int key) {
        return findInsertionIndex(keys, states, key, mask);
    }

    /**
     * Find the index at which a key should be inserted
     * @param keys keys table
     * @param states states table
     * @param key key to lookup
     * @param mask bit mask for hash values
     * @return index at which key should be inserted
     */
    @SuppressWarnings({"index:array.access.unsafe.low", "index:array.access.unsafe.high", "index:argument.type.incompatible"}) /*
    mask is @NonNegative and @LessThan({"this.states.length", "this.keys.length","this.values.length"}) which makes
    index = <variable> & mask also @NonNegative and @LessThan({"this.states.length", "this.keys.length","this.values.length"})
    */
    private static int findInsertionIndex(final int[] keys, final byte[] states,
                                          final int key, final int mask) {
        final int hash = hashOf(key);
        int index = hash & mask;
        if (states[index] == FREE) { // #1
            return index;
        } else if (states[index] == FULL && keys[index] == key) { // #1
            return changeIndexSign(index);
        }

        int perturb = perturb(hash);
        int j = index;
        if (states[index] == FULL) { // #1
            while (true) {
                j = probe(perturb, j);
                index = j & mask;
                perturb >>= PERTURB_SHIFT;

                if (states[index] != FULL || keys[index] == key) { // #1
                    break;
                }
            }
        }

        if (states[index] == FREE) { // #1
            return index;
        } else if (states[index] == FULL) { // #1
            // due to the loop exit condition,
            // if (states[index] == FULL) then keys[index] == key
            return changeIndexSign(index);
        }

        final int firstRemoved = index;
        while (true) {
            j = probe(perturb, j);
            index = j & mask;

            if (states[index] == FREE) { // #1
                return firstRemoved;
            } else if (states[index] == FULL && keys[index] == key) { // #1
                return changeIndexSign(index);
            }

            perturb >>= PERTURB_SHIFT;

        }

    }

    /**
     * Compute next probe for collision resolution
     * @param perturb perturbed hash
     * @param j previous probe
     * @return next probe
     */
    private static int probe(final int perturb, final int j) {
        return (j << 2) + j + perturb + 1;
    }

    /**
     * Change the index sign
     * @param index initial index
     * @return changed index
     */
    private static int changeIndexSign(final int index) {
        return -index - 1;
    }

    /**
     * Get the number of elements stored in the map.
     * @return number of elements stored in the map
     */
    public int size() {
        return size;
    }


    /**
     * Remove the value associated with a key.
     * @param key key to which the value is associated
     * @return removed value
     */
    public T remove(final int key) {

        final int hash  = hashOf(key);
        int index = hash & mask;
        if (containsKey(key, index)) {
            return doRemove(index);
        }

        if (states[index] == FREE) {
            return missingEntries;
        }

        int j = index;
        for (int perturb = perturb(hash); states[index] != FREE; perturb >>= PERTURB_SHIFT) {
            j = probe(perturb, j);
            index = j & mask;
            if (containsKey(key, index)) {
                return doRemove(index);
            }
        }

        return missingEntries;

    }

    /**
     * Check if the tables contain an element associated with specified key
     * at specified index.
     * @param key key to check
     * @param index index to check
     * @return true if an element is associated with key at index
     */
    private boolean containsKey(final int key, final @IndexFor({"this.states", "this.values", "this.keys"}) int index) {
        return (key != 0 || states[index] == FULL) && keys[index] == key;
    }

    /**
     * Remove an element at specified index.
     * @param index index of the element to remove
     * @return removed value
     */
    private T doRemove(@IndexFor({"this.states", "this.values", "this.keys"}) int index) {
        keys[index]   = 0;
        states[index] = REMOVED;
        final T previous = values[index];
        values[index] = missingEntries;
        --size;
        ++count;
        return previous;
    }

    /**
     * Put a value associated with a key in the map.
     * @param key key to which value is associated
     * @param value value to put in the map
     * @return previous value associated with the key
     */
    @SuppressWarnings({"index:array.access.unsafe.low", "index:array.access.unsafe.high"}) /*
    #1: findInsertionIndex() returns (<variable> & mask) or changeIndexSign(<variable> & mask) whose magnitude is @LessThan({"this.values.length", "this.states.length", "this.keys.length"})
    as mask is @LessThan({"this.values.length", "this.states", "this.keys.length"}). The possibility of negative index has been checked and then index is made positive with the same magnitude
    */
    public T put(final int key, final T value) {
        int index = findInsertionIndex(key);
        T previous = missingEntries;
        boolean newMapping = true;
        if (index < 0) {
            index = changeIndexSign(index);
            previous = values[index];
            newMapping = false;
        }
        keys[index]   = key; // #1
        states[index] = FULL; // #1
        values[index] = value; // #1
        if (newMapping) {
            ++size;
            if (shouldGrowTable()) {
                growTable();
            }
            ++count;
        }
        return previous;

    }

    /**
     * Grow the tables.
     */
    @SuppressWarnings({"index:array.access.unsafe.low", "index:array.access.unsafe.high", "index:assignment.type.incompatible"}) /*
    #1: the new arrays created have a greater length than the old arrays by #0.1, hence, states[index] will not be full,
        hence a positive index will be returned (look at implementaion of findInsertionIndex())
    #2: All the arrays are defined with the same length, hence the annotation is retained. Also, mask = newLength - 1 < newLength which is the length of the new arrays
    */
    private void growTable() {

        final int oldLength      = states.length;
        final int[] oldKeys      = keys;
        final T[] oldValues = values;
        final byte[] oldStates   = states;

        final int newLength = RESIZE_MULTIPLIER * oldLength; // #0.1
        final int[] newKeys = new int[newLength];
        final T[] newValues = buildArray(newLength);
        final byte[] newStates = new byte[newLength];
        final int newMask = newLength - 1;
        for (int i = 0; i < oldLength; ++i) {
            if (oldStates[i] == FULL) {
                final int key = oldKeys[i];
                final int index = findInsertionIndex(newKeys, newStates, key, newMask);
                newKeys[index]   = key; // #1
                newValues[index] = oldValues[i]; // #1
                newStates[index] = FULL; // #1
            }
        }

        mask   = newMask; // #2
        keys   = newKeys; // #2
        values = newValues; // #2
        states = newStates; // #2

    }

    /**
     * Check if tables should grow due to increased size.
     * @return true if  tables should grow
     */
    private boolean shouldGrowTable() {
        return size > (mask + 1) * LOAD_FACTOR;
    }

    /**
     * Compute the hash value of a key
     * @param key key to hash
     * @return hash value of the key
     */
    private static int hashOf(final int key) {
        final int h = key ^ ((key >>> 20) ^ (key >>> 12));
        return h ^ (h >>> 7) ^ (h >>> 4);
    }


    /** Iterator class for the map. */
    public class Iterator {

        /** Reference modification count. */
        private final int referenceCount;

        /** Index of current element. */
        private @LTLengthOf({"this.states", "this.keys", "this.values"}) int current;

        /** Index of next element. */
        private @LTLengthOf(value = {"this.states", "this.keys", "this.values"}, offset = {"-1", "-1", "-1"}) int next;

        /**
         * Simple constructor.
         */
        private Iterator() {

            // preserve the modification count of the map to detect concurrent modifications later
            referenceCount = count;

            // initialize current index
            next = -1;
            try {
                advance();
            } catch (NoSuchElementException nsee) { // NOPMD
                // ignored
            }

        }

        /**
         * Check if there is a next element in the map.
         * @return true if there is a next element
         */
        public boolean hasNext() {
            return next >= 0;
        }

        /**
         * Get the key of current entry.
         * @return key of current entry
         * @exception ConcurrentModificationException if the map is modified during iteration
         * @exception NoSuchElementException if there is no element left in the map
         */
        public int key()
            throws ConcurrentModificationException, NoSuchElementException {
            if (referenceCount != count) {
                throw new ConcurrentModificationException();
            }
            if (current < 0) {
                throw new NoSuchElementException();
            }
            return keys[current];
        }

        /**
         * Get the value of current entry.
         * @return value of current entry
         * @exception ConcurrentModificationException if the map is modified during iteration
         * @exception NoSuchElementException if there is no element left in the map
         */
        public T value()
            throws ConcurrentModificationException, NoSuchElementException {
            if (referenceCount != count) {
                throw new ConcurrentModificationException();
            }
            if (current < 0) {
                throw new NoSuchElementException();
            }
            return values[current];
        }

        /**
         * Advance iterator one step further.
         * @exception ConcurrentModificationException if the map is modified during iteration
         * @exception NoSuchElementException if there is no element left in the map
         */
        @SuppressWarnings({"index:assignment.type.incompatible", "index:array.access.unsafe.low", "index:array.access.unsafe.high", "index:unary.increment.type.incompatible"}) /*
        #1: These statement is never executed with next = states.length because when next = states.length - 1, the try catch block makes next = -2
        */
        public void advance()
            throws ConcurrentModificationException, NoSuchElementException {

            if (referenceCount != count) {
                throw new ConcurrentModificationException();
            }

            // advance on step
            current = next;

            // prepare next step
            try {
                while (states[++next] != FULL) { // NOPMD
                    // nothing to do
                }
            } catch (ArrayIndexOutOfBoundsException e) {
                next = -2;
                if (current < 0) {
                    throw new NoSuchElementException();
                }
            }

        }

    }

    /**
     * Read a serialized object.
     * @param stream input stream
     * @throws IOException if object cannot be read
     * @throws ClassNotFoundException if the class corresponding
     * to the serialized object cannot be found
     */
    private void readObject(final ObjectInputStream stream)
        throws IOException, ClassNotFoundException {
        stream.defaultReadObject();
        count = 0;
    }

    /** Build an array of elements.
     * @param length size of the array to build
     * @return a new array
     */
    @SuppressWarnings("unchecked") // field is of type T
    private T[] buildArray(final @NonNegative int length) {
        return (T[]) Array.newInstance(field.getRuntimeClass(), length);
    }

}
