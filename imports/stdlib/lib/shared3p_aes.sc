/*
 * Copyright (C) 2015 Cybernetica
 *
 * Research/Commercial License Usage
 * Licensees holding a valid Research License or Commercial License
 * for the Software may use this file according to the written
 * agreement between you and Cybernetica.
 *
 * GNU Lesser General Public License Usage
 * Alternatively, this file may be used under the terms of the GNU Lesser
 * General Public License version 3 as published by the Free Software
 * Foundation and appearing in the file LICENSE.LGPLv3 included in the
 * packaging of this file.  Please review the following information to
 * ensure the GNU Lesser General Public License version 3 requirements
 * will be met: http://www.gnu.org/licenses/lgpl-3.0.html.
 *
 * For further information, please contact us at sharemind@cyber.ee.
 */

/**
* \cond
*/
module shared3p_aes;

import stdlib;
import shared3p;
import shared3p_random;
/**
* \endcond
*/

/**
 * \cond
 */
uint AES128_Nk = 4;
uint AES192_Nk = 6;
uint AES256_Nk = 8;

uint AES128_Nb = 4;
uint AES192_Nb = 4;
uint AES256_Nb = 4;

uint AES128_Nr = 10;
uint AES192_Nr = 12;
uint AES256_Nr = 14;
/**
 * \endcond
 */


/**
* @file
* \defgroup shared3p_aes shared3p_aes.sc
* \defgroup aes_genkey aesGenkey
* \defgroup aes_expandkey aesExpandKey
* \defgroup aes_encrypt aesEncryptEcb
*/

/** \addtogroup shared3p_aes
*@{
* @brief Module with AES128/192/256 functions
*/

/*******************************************************************************
********************************************************************************
**                                                                            **
**  AES128                                                                    **
**                                                                            **
********************************************************************************
*******************************************************************************/

/** \addtogroup aes_genkey
 *  @{
 *  @brief Function for generating a key for AES encryption
 *  @param blocks - an \ref uint64 "uint" type value
 *  @return returns a vector of type \ref xor_uint32 "xor_uint32" with a randomly generated key
 */

/**
*  @pre ( \ref uint64 "uint" max value ) / AES128_Nk >= blocks
*/
template <domain D : shared3p>
D xor_uint32[[1]] aes128Genkey(uint blocks) {
    assert(UINT64_MAX / AES128_Nk >= blocks); // Check for overflow
    D xor_uint32[[1]] r (blocks * AES128_Nk);
    r = randomize(r);
    return r;
}

/** @}*/
/** \addtogroup aes_expandkey
 *  @{
 *  @brief Function for expanding a randomly generated AES key
 *  @param aeskey - a 1-dimensional array of type \ref xor_uint32 "xor_uint32". See also \ref aes_genkey "aesGenkey"
 *  @return returns a vector of type \ref xor_uint32 "xor_uint32" with an expanded key
 */

/**
*  @pre the size of **aeskey** has to be dividable by AES128_Nk
*/
template <domain D : shared3p>
D xor_uint32[[1]] aes128ExpandKey(D xor_uint32[[1]] aeskey) {
    assert((size(aeskey) % AES128_Nk) == 0);
    D xor_uint32[[1]] expandedKey (size(aeskey) * (AES128_Nr + 1));
    __syscall("shared3p::aes128_xor_uint32_vec_expand_key", __domainid(D), aeskey, expandedKey);
    return expandedKey;
}

/** @}*/
/** \addtogroup aes_encrypt
 *  @{
 *  @brief Function for encrypting with AES algorithm
 *  @return returns a vector of type \ref xor_uint32 "xor_uint32" with the encrypted values
 */


/**
* @param expandedKey - an aes128 expanded key of type \ref xor_uint32 "xor_uint32". See also \ref aes_genkey "aesGenkey" and \ref aes_expandkey "aesExpandKey"
* @param plainText - a \ref string "string" converted to a \ref xor_uint32 "xor_uint32" vector
* @pre the size of **expandedKey** has to be dividable by (AES128_Nb * (AES128_Nr + 1))
* @pre the size of **plainText** has to be dividable by AES128_Nb
* @pre ( **plainText** / AES128_Nb ) == ( size of **expandedKey** ) / (AES128_Nb * (AES128_Nr + 1))
*/
template <domain D : shared3p>
D xor_uint32[[1]] aes128EncryptEcb(D xor_uint32[[1]] expandedKey, D xor_uint32[[1]] plainText) {
    assert(size(plainText) > 0);
    assert((size(expandedKey) % (AES128_Nb * (AES128_Nr + 1))) == 0);
    assert((size(plainText) % AES128_Nb) == 0);
    assert((size(plainText) / AES128_Nb) == (size(expandedKey) / (AES128_Nb * (AES128_Nr + 1))));
    D xor_uint32[[1]] cipherText (size(plainText));
    __syscall("shared3p::aes128_xor_uint32_vec", __domainid(D), plainText, expandedKey, cipherText);
    return cipherText;
}

/**
* @param expandedKey - an aes128 expanded key of type \ref xor_uint32 "xor_uint32". See also \ref aes_genkey "aesGenkey" and \ref aes_expandkey "aesExpandKey"
* @param plainText - a \ref string "string" converted to a \ref xor_uint32 "xor_uint32" vector
* @pre the size of **plainText** has to be dividable by AES128_Nb
* @pre the size of **expandedKey** has to be (AES128_Nb * (AES128_Nr + 1))
*/
template <domain D : shared3p>
D xor_uint32[[1]] aes128SingleKeyEncryptEcb(D xor_uint32[[1]] expandedKey, D xor_uint32[[1]] plainText) {
    assert(size(plainText) > 0);
    assert((size(plainText) % AES128_Nb) == 0);
    assert(size(expandedKey) == (AES128_Nb * (AES128_Nr + 1)));
    D xor_uint32[[1]] cipherText (size(plainText));
    __syscall("shared3p::aes128_single_key_xor_uint32_vec", __domainid(D), plainText, expandedKey, cipherText);
    return cipherText;
}

/** @}*/

/*******************************************************************************
********************************************************************************
**                                                                            **
**  AES192                                                                    **
**                                                                            **
********************************************************************************
*******************************************************************************/


/** \addtogroup aes_genkey
 *  @{
 */

/**
*  @pre ( \ref uint64 "uint" max value ) / AES192_Nk >= blocks
*/

template <domain D : shared3p>
D xor_uint32[[1]] aes192Genkey(uint blocks) {
    assert(UINT64_MAX / AES192_Nk >= blocks); // Check for overflow
    D xor_uint32[[1]] r (blocks * AES192_Nk);
    r = randomize(r);
    return r;
}

/** @}*/
/** \addtogroup aes_expandkey
 *  @{
 */

/**
*  @pre the size of **aeskey** has to be dividable by AES192_Nk
*/

template <domain D : shared3p>
D xor_uint32[[1]] aes192ExpandKey(D xor_uint32[[1]] aeskey) {
    assert((size(aeskey) % AES192_Nk) == 0);
    D xor_uint32[[1]] expandedKey ((size(aeskey) / AES192_Nk) * AES192_Nb * (AES192_Nr + 1));
    __syscall("shared3p::aes192_xor_uint32_vec_expand_key", __domainid(D), aeskey, expandedKey);
    return expandedKey;
}

/** @}*/
/** \addtogroup aes_encrypt
 *  @{
 */


/**
* @param expandedKey - an aes192 expanded key of type \ref xor_uint32 "xor_uint32". See also \ref aes_genkey "aesGenkey" and \ref aes_expandkey "aesExpandKey"
* @param plainText - a \ref string "string" converted to a \ref xor_uint32 "xor_uint32" vector
* @pre the size of **expandedKey** has to be dividable by (AES192_Nb * (AES192_Nr + 1))
* @pre the size of **plainText** has to be dividable by AES192_Nb
* @pre ( **plainText** / AES192_Nb ) == ( size of **expandedKey** ) / (AES192_Nb * (AES192_Nr + 1))
*/

template <domain D : shared3p>
D xor_uint32[[1]] aes192EncryptEcb(D xor_uint32[[1]] expandedKey, D xor_uint32[[1]] plainText) {
    assert(size(plainText) > 0);
    assert((size(expandedKey) % (AES192_Nb * (AES192_Nr + 1))) == 0);
    assert((size(plainText) % AES192_Nb) == 0);
    assert((size(plainText) / AES192_Nb) == (size(expandedKey) / (AES192_Nb * (AES192_Nr + 1))));
    D xor_uint32[[1]] cipherText (size(plainText));
    __syscall("shared3p::aes192_xor_uint32_vec", __domainid(D), plainText, expandedKey, cipherText);
    return cipherText;
}

/** @}*/

/*******************************************************************************
********************************************************************************
**                                                                            **
**  AES256                                                                    **
**                                                                            **
********************************************************************************
*******************************************************************************/

/** \addtogroup aes_genkey
 *  @{
 */

/**
*  @pre ( \ref uint64 "uint" max value ) / AES256_Nk >= blocks
*/

template <domain D : shared3p>
D xor_uint32[[1]] aes256Genkey(uint blocks) {
    assert(UINT64_MAX / AES256_Nk >= blocks); // Check for overflow
    D xor_uint32[[1]] r (blocks * AES256_Nk);
    r = randomize(r);
    return r;
}

/** @}*/
/** \addtogroup aes_expandkey
 *  @{
 */

/**
*  @pre the size of **aeskey** has to be dividable by AES256_Nk
*/

template <domain D : shared3p>
D xor_uint32[[1]] aes256ExpandKey(D xor_uint32[[1]] aeskey) {
    assert((size(aeskey) % AES256_Nk) == 0);
    D xor_uint32[[1]] expandedKey ((size(aeskey) / AES256_Nk) * AES256_Nb * (AES256_Nr + 1));
    __syscall("shared3p::aes256_xor_uint32_vec_expand_key", __domainid(D), aeskey, expandedKey);
    return expandedKey;
}

/** @}*/
/** \addtogroup aes_encrypt
 *  @{
 */


/**
* @param expandedKey - an aes256 expanded key of type \ref xor_uint32 "xor_uint32". See also \ref aes_genkey "aesGenkey" and \ref aes_expandkey "aesExpandKey"
* @param plainText - a \ref string "string" converted to a \ref xor_uint32 "xor_uint32" vector
* @pre the size of **expandedKey** has to be dividable by (AES256_Nb * (AES256_Nr + 1))
* @pre the size of **plainText** has to be dividable by AES256_Nb
* @pre ( **plainText** / AES256_Nb ) == ( size of **expandedKey** ) / (AES256_Nb * (AES256_Nr + 1))
*/

template <domain D : shared3p>
D xor_uint32[[1]] aes256EncryptEcb(D xor_uint32[[1]] expandedKey, D xor_uint32[[1]] plainText) {
    assert(size(plainText) > 0);
    assert((size(expandedKey) % (AES256_Nb * (AES256_Nr + 1))) == 0);
    assert((size(plainText) % AES256_Nb) == 0);
    assert((size(plainText) / AES256_Nb) == (size(expandedKey) / (AES256_Nb * (AES256_Nr + 1))));
    D xor_uint32[[1]] cipherText (size(plainText));
    __syscall("shared3p::aes256_xor_uint32_vec", __domainid(D), plainText, expandedKey, cipherText);
    return cipherText;
}

/** @}*/
/** @}*/
