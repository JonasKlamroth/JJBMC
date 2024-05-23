/*
 * Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may not use this file except
 * in compliance with the License. A copy of the License is located at
 *
 * http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 */

package com.amazonaws.encryptionsdk.model;

import java.nio.ByteBuffer;
import java.util.Arrays;

/**
 * This class implements the headers for the encrypted content stored in a
 * single block. These headers are parsed and used when the encrypted content
 * in the single block is decrypted.
 *
 * <p>
 * It contains the following fields in order:
 * <ol>
 * <li>nonce</li>
 * <li>length of content</li>
 * </ol>
 */
//@ non_null_by_default
public final class CipherBlockHeaders {
    //@ spec_public nullable
    private byte[] nonce_ = null;
    //@ spec_public
    private long contentLength_ = -1;

    // This is set after the nonce length is parsed in the CiphertextHeaders
    // during decryption. This can be set only using its setter.
    //@ spec_public
    private short nonceLength_ = 0;
    //@ public invariant nonceLength_ >= 0;

    //@ spec_public
    private boolean isComplete_ = false;

    /**
     * Default constructor.
     */
    //@ public normal_behavior
    //@   ensures nonce_ == null;
    //@   ensures contentLength_ == -1;
    //@   ensures nonceLength_ == 0;
    //@   ensures isComplete_ == false;
    public CipherBlockHeaders() {
    }

    /**
     * Construct the single block headers using the provided nonce
     * and length of content.
     *
     * @param nonce
     *            the bytes containing the nonce.
     * @param contentLen
     *            the length of the content in the block.
     */
    //@ public normal_behavior
    //@   requires nonce != null && nonce.length <= 5;
    //@   ensures nonce_.length == nonce.length;
    //@   ensures (\forall int i; i >= 0 && i < nonce.length; nonce_[i] == nonce[i]);
    //@   ensures contentLength_ == contentLen;
    //@   ensures nonceLength_ == 0;
    //@   ensures isComplete_ == false;
    public CipherBlockHeaders(final byte[] nonce, final long contentLen) {
        if (nonce == null) {
            assert false;
            return;
        }
        if (nonce.length > 5) {
            assert false;
            return;
        }

        nonce_ = nonce.clone();
        contentLength_ = contentLen;
    }

    /**
     * Serialize the header into a byte array.
     *
     * @return
     *         the serialized bytes of the header.
     */
    /*@ public normal_behavior
      @   requires nonce_ != null;
      @   requires nonce_.length <= Integer.MAX_VALUE - (Long.SIZE / Byte.SIZE);
      @   ensures \result.length == nonce_.length + (Long.SIZE / Byte.SIZE);
      @   ensures (\forall int i; 0<=i && i<nonce_.length; \result[i] == nonce_[i]);
      @ pure
      @*/
    public byte[] toByteArray() {
        final int outLen = nonce_.length + (Long.SIZE / Byte.SIZE);
        final ByteBuffer out = ByteBuffer.allocate(outLen);

        out.put(nonce_);
        out.putLong(contentLength_);

        return out.array();
    }

    /**
     * Parse the nonce in the provided bytes. It looks for bytes of size
     * defined by the nonce length in the provided bytes starting at the
     * specified off.
     *
     * <p>
     * If successful, it returns the size of the parsed bytes which is the nonce
     * length. On failure, it throws a parse exception.
     *
     * @param b
     *            the byte array to parse.
     * @param off
     *            the offset in the byte array to use when parsing.
     * @return
     *         the size of the parsed bytes which is the nonce length.
     * @throws Exception
     *             if there are not sufficient bytes to parse the nonce.
     */
    //@ private normal_behavior
    //@   requires nonceLength_ > 0;
    //@   requires 0 < off;
    //@   requires b != null;
    //@   requires b.length - off >= nonceLength_;
    //@   assignable nonce_;
    //@   ensures nonce_ != null;
    //@   ensures \result == nonceLength_;
    private int parseNonce(final byte[] b, final int off) throws Exception {
        final int bytesToParseLen = b.length - off;
        if (bytesToParseLen >= nonceLength_) {
            nonce_ = Arrays.copyOfRange(b, off, off + nonceLength_);
            return nonceLength_;
        } else {
            assert false;
            return -1;
        }
    }

    /**
     * Parse the content length in the provided bytes. It looks for 8 bytes
     * representing a long primitive type in the provided bytes starting at the
     * specified off.
     *
     * <p>
     * If successful, it returns the size of the parsed bytes which is the size
     * of the long primitive type. On failure, it throws a parse exception.
     *
     * @param b
     *            the byte array to parse.
     * @param off
     *            the offset in the byte array to use when parsing.
     * @return
     *         the size of the parsed bytes which is the size of the long
     *         primitive type.
     * @throws Exception
     *             if there are not sufficient bytes to parse the content
     *             length.
     */

    /**
     * Check if this object has all the header fields populated and available
     * for reading.
     *
     * @return
     *         true if this object containing the single block header fields
     *         is complete; false otherwise.
     */
    //@ public normal_behavior
    //@   ensures \result == isComplete_;
    //@ pure
    public boolean isComplete() {
        return isComplete_;
    }

    /**
     * Return the nonce set in the single block header.
     *
     * @return
     *         the bytes containing the nonce set in the single block header.
     */
    //@   requires nonce_ != null;
    //@   ensures \result != null;
    //@   ensures \result != null;
    //@   ensures \result.length == nonce_.length;
    //@   ensures (\forall int i; i >= 0 && i < nonce_.length; nonce_[i] == \result[i]);
    public byte[] getNonce() {
        return nonce_ != null ? nonce_.clone() : null;
    }

    /**
     * Return the content length set in the single block header.
     *
     * @return
     *         the content length set in the single block header.
     */
    //@ public normal_behavior
    //@   ensures \result == contentLength_;
    //@ pure
    public long getContentLength() {
        return contentLength_;
    }

    /**
     * Set the length of the nonce used in the encryption of the content stored
     * in the single block.
     *
     * @param nonceLength
     *            the length of the nonce used in the encryption of the content
     *            stored in the single block.
     */
    //@ public normal_behavior
    //@   requires nonceLength >= 0;
    //@   assignable nonceLength_;
    //@   ensures nonceLength_ == nonceLength;
    public void setNonceLength(final short nonceLength) {
        nonceLength_ = nonceLength;
    }
}