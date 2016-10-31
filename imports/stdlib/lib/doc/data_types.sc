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

@page data_types Data types
@brief Different data types of the SecreC language


@section string string

A regular string exactly like in c++, c ,java etc.
  
@section bool boolean

| Bool   | Numerical |
| :----: | :-------: |
| true   | 1 | 
| false  | 0 | 

@section uint Unsigned integer
@subsection uint8 uint8

|        |            |
| :----: | :-------:  |
| Maximum value | 255 | 
| Minimum value | 0   | 

@subsection uint16 uint16

|        |            |
| :----: | :-------:  |
| Maximum value | 65535 | 
| Minimum value | 0   | 

@subsection uint32 uint32

|        |            |
| :----: | :-------:  |
| Maximum value | 4294967295 | 
| Minimum value | 0   | 

@subsection uint64 uint64/uint

|        |            |
| :----: | :-------:  |
| Maximum value | 18446744073709551615 | 
| Minimum value | 0   |

@note in the language reference **uint64** and **uint** are considered the same and can be declared in either way  

@section int Signed integer
@subsection int8 int8

|        |            |
| :----: | :-------:  |
| Maximum value | 127 | 
| Minimum value | -128 | 

@subsection int16 int16

|        |            |
| :----: | :-------:  |
| Maximum value | 32767 | 
| Minimum value | -32768  | 

@subsection int32 int32

|        |            |
| :----: | :-------:  |
| Maximum value | 2147483647 | 
| Minimum value | -2147483648 | 

@subsection int64 int64/int

|        |            |
| :----: | :-------:  |
| Maximum value | 9223372036854775807 | 
| Minimum value | -9223372036854775808 |

@note in the language reference **int64** and **int** are considered the same and can be declared in either way  

@section xor_uint XOR Unsigned integer
@subsection xor_uint8 xor_uint8

|        |            |
| :----: | :-------:  |
| Maximum value | 255 | 
| Minimum value | 0   | 

@subsection xor_uint16 xor_uint16

|        |            |
| :----: | :-------:  |
| Maximum value | 65535 | 
| Minimum value | 0   | 

@subsection xor_uint32 xor_uint32

|        |            |
| :----: | :-------:  |
| Maximum value | 4294967295 | 
| Minimum value | 0   | 

@subsection xor_uint64 xor_uint64

|        |            |
| :----: | :-------:  |
| Maximum value | 18446744073709551615 | 
| Minimum value | 0   |


@section float Floating point number
@subsection float32 float32/float

|        |            |
| :----: | :-------:  |
| Maximum positive value | \f[3.402823 \times 10^{38}\f] | 
| Minimum positive value | \f[2.802597 \times 10^{-45}\f] | 
| Maximum negative value | \f[-3.402823 \times 10^{38}\f] | 
| Minimum negative value | \f[-2.802597 \times 10^{-45}\f] | 


@subsection float64 float64

|        |            |
| :----: | :-------:  |
| Maximum positive value | \f[1.797693 \times 10^{308}\f] |
| Minimum positive value | \f[4.940656 \times 10^{-324}\f] |
| Maximum negative value | \f[-1.797693 \times 10^{308}\f] |
| Minimum negative value | \f[-4.940656 \times 10^{-324}\f] |

@note in the language reference **float32** and **float** are considered the same and can be declared in either way  

*/
