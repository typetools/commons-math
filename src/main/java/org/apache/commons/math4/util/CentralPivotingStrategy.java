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

import java.io.Serializable;

import org.apache.commons.math4.exception.MathIllegalArgumentException;

import org.checkerframework.checker.index.qual.IndexFor;
import org.checkerframework.checker.index.qual.LTEqLengthOf;
import org.checkerframework.checker.index.qual.Positive;
import org.checkerframework.checker.index.qual.LessThan;


/**
 * A mid point strategy based on the average of begin and end indices.
 * @since 3.4
 */
public class CentralPivotingStrategy implements PivotingStrategyInterface, Serializable {

    /** Serializable UID. */
    private static final long serialVersionUID = 20140713L;

    /**
     * {@inheritDoc}
     * This in particular picks a average of begin and end indices
     * @return The index corresponding to a simple average of
     * the first and the last element indices of the array slice
     * @throws MathIllegalArgumentException when indices exceeds range
     */
    @Override
    @SuppressWarnings("index:return.type.incompatible") // #1: begin + (end - begin)/2 = (begin + end)/2 where begin and end are @IndexFor("work"), hence, (begin + end)/2 is @IndexFor("work")
    public @IndexFor("#1") int pivotIndex(final double[] work, final @LessThan("#3") @IndexFor("#1") int begin, final @Positive @LTEqLengthOf("#1") int end)
        throws MathIllegalArgumentException {
        MathArrays.verifyValues(work, begin, end-begin);
        return begin + (end - begin)/2; // #1
    }

}
