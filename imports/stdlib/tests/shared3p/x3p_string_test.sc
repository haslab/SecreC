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

import stdlib;
import shared3p;
import shared3p_random;
import shared3p_string;
import test_utility;

domain pd_shared3p shared3p;

void main(){
    string test_prefix = "string to xor_uint8 vector and back to string";
    {
        string test = "The quick brown fox jumps over the lazy dog";
        pd_shared3p xor_uint8[[1]] control (43) = {84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103};
        pd_shared3p xor_uint8[[1]] str = bl_str(test);

        test(test_prefix, all(declassify(str == control)));

        string test2 = bl_strDeclassify(str);
        test(test_prefix, test == test2);
    }

    test_prefix = "CRC16/32 hash generation with initial hash 0";
    {
        string test = "The quick brown fox jumps over the lazy dog";
        pd_shared3p xor_uint8[[1]] str = bl_str(test);

        pd_shared3p xor_uint32 hash = CRC32(str);
        pd_shared3p xor_uint32 control = 1095738169;

        test(test_prefix, declassify(hash == control));

        pd_shared3p xor_uint16 hash2 = CRC16(str);
        pd_shared3p xor_uint16 control2 = 64735;

        test(test_prefix, declassify(hash == control));
    }

    test_prefix = "Count zeroes function";
    {
        pd_shared3p xor_uint8[[1]] str (15) = 0;
        test(test_prefix, declassify(countZeroes(str)) == 15);

        str = {0, 2, 0, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0};
        test(test_prefix, declassify(countZeroes(str)) == 8);
    }

    test_prefix = "Bounded length string is empty ";
    {
        pd_shared3p xor_uint8[[1]] str (15) = 0;
        test(test_prefix + "(15 x 0 is empty)", declassify(bl_strIsEmpty(str)));

        str = {0};
        test(test_prefix + "({0} is empty)", declassify(bl_strIsEmpty(str)));

        str = {1};
        test(test_prefix + "({1} is not empty)", !declassify(bl_strIsEmpty(str)));

        str = reshape(0, 0); // {}; // does not work
        test(test_prefix + "({} is empty)", declassify(bl_strIsEmpty(str)));

        str = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 0, 0, 0, 0};
        test(test_prefix + "({1 .. 10, 0, 0, 0, 0, 0} is not empty)", !declassify(bl_strIsEmpty(str)));
    }

    test_prefix = "Bounded string length function";
    {
        pd_shared3p xor_uint8[[1]] str (43) = {84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103};
        pd_shared3p uint length = bl_strLength(str);
        test(test_prefix, declassify(length) == 43);
    }

    test_prefix = "Bounded string trimming function";
    {
        pd_shared3p xor_uint8[[1]] str (43) = {84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,0,0,0,0,0,0,0,0,0,0,0,0,0};

        pd_shared3p uint length = bl_strLength(bl_strTrim(str));
        test(test_prefix, declassify(length) == 30);
    }

    test_prefix = "2 string are equal function";
    {
        pd_shared3p xor_uint8[[1]] str (43) = {84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103};
        pd_shared3p xor_uint8[[1]] str2 (43) = {84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103};
        pd_shared3p xor_uint8[[1]] str3 (50) = {84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103,0,0,0,0,0,0,0};
        test(test_prefix, declassify(bl_strEquals(str,str2)) && declassify(bl_strEquals(str,str3)) && declassify(bl_strEquals(str3,str2)));
    }

    test_prefix = "Sorting permutation function";
    {
        pd_shared3p bool[[1]] temp (6);
        temp = randomize(temp);
        pd_shared3p uint[[1]] temp2 = findSortingPermutation(temp);
        uint[[1]] permutation = declassify(temp2);
        bool[[1]] vec = declassify(temp);
        bool[[1]] vec2 (6);
        for(uint i = 0; i < 6;++i){
            for(uint j = 0; j < 6; ++j){
                if(permutation[j] == i){
                    vec2[i] = vec[j];
                    break;
                }
            }
        }
        bool result = true;
        bool last;
        for(uint i = 0; i < 6; ++i){
            if(i == 0){
                last = vec2[i];
            }
            else{
                if(last == false && vec2[i] == true){
                    result = false;
                    break;
                }
                else{
                    last = vec2[i];
                }
            }
        }

        test(test_prefix, result);
    }

    test_prefix = "String concatenation";
    {
        pd_shared3p xor_uint8[[1]] str (21) = {84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106};
        pd_shared3p xor_uint8[[1]] str2 (22) = {117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103};
        pd_shared3p xor_uint8[[1]] control (43) = {84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103};
        pd_shared3p xor_uint8[[1]] str3 = bl_strCat(str,str2);
        test(test_prefix, all(declassify(str3 == control)));
    }

    test_prefix = "String zero extend function";
    {
        pd_shared3p xor_uint8[[1]] str (3) =  {84,104,101};
        pd_shared3p xor_uint8[[1]] str2 = zeroExtend(str,8::uint);
        pd_shared3p xor_uint8[[1]] str3 = {84,104,101,0,0,0,0,0};
        test(test_prefix, declassify(bl_strEquals(str,str2)) && declassify(countZeroes(str2) == 5));
    }

    test_prefix = "string alphabetizing function";
    {
        string str = "This is a test";
        string str2 = "This is also a test";
        pd_shared3p xor_uint8[[1]] vec = bl_str(str);
        pd_shared3p xor_uint8[[1]] vec2 = bl_str(str2);
        test(test_prefix, declassify(bl_strIsLessThan(vec,vec2)));

        str = "aaaaabbbccdd";
        str2 = "aaaaaaaaaaaa";
        vec = bl_str(str);
        vec2 = bl_str(str2);
        test(test_prefix, declassify(bl_strIsLessThan(vec2,vec)));
    }

    test_prefix = "Levenshtein distance";
    {
        string str = "this is a test";
        string str2 = "these are two tests";
        pd_shared3p xor_uint8[[1]] vec = bl_str(str);
        pd_shared3p xor_uint8[[1]] vec2 = bl_str(str2);
        pd_shared3p uint distance = bl_strLevenshtein(vec,vec2);
        test(test_prefix, declassify(distance) == 9);
    }

    test_prefix = "String contains function";
    {
        string str = "The quick brown fox jumps over the lazy dog";
        pd_shared3p xor_uint8[[1]] vec = bl_str(str);
        string sub_str = "k brown f";
        pd_shared3p xor_uint8[[1]] vec2 = bl_str(sub_str);
        string sub_str2 = "mps over th";
        pd_shared3p xor_uint8[[1]] vec3 = bl_str(sub_str2);
        test(test_prefix, declassify(bl_strContains(vec,vec2)) && declassify(bl_strContains(vec,vec3)));

        str = "The quick brown fox jumps over the lazy dog";
        vec = bl_str(str);
        sub_str = "The quic";
        vec2 = bl_str(sub_str);
        sub_str2 = "y dog";
        vec3 = bl_str(sub_str2);
        test(test_prefix, declassify(bl_strContains(vec,vec2)) && declassify(bl_strContains(vec,vec3)));
    }

    test_prefix = "Index of pattern in string";
    {
        string str = "The quick brown fox jumps over the lazy dog";
        pd_shared3p xor_uint8[[1]] vec = bl_str(str);
        string sub_str = "ck brown fo";
        pd_shared3p xor_uint8[[1]] vec2 = bl_str(sub_str);
        string sub_str2 = "r the laz";
        pd_shared3p xor_uint8[[1]] vec3 = bl_str(sub_str2);
        pd_shared3p uint index = bl_strIndexOf(vec,vec2);
        pd_shared3p uint index2 = bl_strIndexOf(vec,vec3);
        test(test_prefix, declassify(index) == 7 && declassify(index2) == 29);
    }

    test_prefix = "String hamming test";
    {
        string str = "this is a test";
        pd_shared3p xor_uint8[[1]] vec = bl_str(str);
        string str2 = "this a test is";
        pd_shared3p xor_uint8[[1]] vec2 = bl_str(str2);
        pd_shared3p uint hammed = bl_strHamming(vec,vec2);
        test(test_prefix, declassify(hammed) == 8);

        str = "this is a test";
        vec = bl_str(str);
        str2 = "tset a si siht";
        vec2 = bl_str(str2);
        hammed = bl_strHamming(vec,vec2);
        test(test_prefix, declassify(hammed) == 10);
    }

    test_prefix = "known string to xor_uint8 vector";
    {
        string test = "The quick brown fox jumps over the lazy dog";
        pd_shared3p xor_uint8[[1]] control (43) = {84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103};
        pd_shared3p xor_uint8[[1]] str = kl_str(test);

        test(test_prefix, all(declassify(str == control)));
    }

    test_prefix = "Xor_uint8 vector to known string";
    {
        string test = "The quick brown fox jumps over the lazy dog";
        pd_shared3p xor_uint8[[1]] str = {84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103};
        string test2 = kl_strDeclassify(str);
        test(test_prefix, test == test2);
    }

    test_prefix = "Known string length function";
    {
        pd_shared3p xor_uint8[[1]] str (43) = {84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103};
        uint length = kl_strLength(str);
        test(test_prefix, length == 43);
    }

    test_prefix = "Known strings are equal function";
    {
        pd_shared3p xor_uint8[[1]] str (43) = {84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103};
        pd_shared3p xor_uint8[[1]] str2 (43) = {84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103};
        test(test_prefix, declassify(kl_strEquals(str,str2)));
    }

    test_prefix = "Known strings alphabetizing function";
    {
        string str = "This is a test";
        string str2 = "This is also a test";
        pd_shared3p xor_uint8[[1]] vec = kl_str(str);
        pd_shared3p xor_uint8[[1]] vec2 = kl_str(str2);
        test(test_prefix, declassify(kl_strIsLessThan(vec,vec2)));

        str = "aaaaabbbccdd";
        str2 = "aaaaaaaaaaaa";
        vec = kl_str(str);
        vec2 = kl_str(str2);
        test(test_prefix, declassify(kl_strIsLessThan(vec2,vec)));
    }

    test_prefix = "2 Known string concatenation";
    {
        pd_shared3p xor_uint8[[1]] str (21) = {84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106};
        pd_shared3p xor_uint8[[1]] str2 (22) = {117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103};
        pd_shared3p xor_uint8[[1]] control (43) = {84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103};
        pd_shared3p xor_uint8[[1]] str3 = kl_strCat(str,str2);
        test(test_prefix, all(declassify(str3 == control)));
    }

    test_prefix = "Known string contains pattern function";
    {
        string str = "The quick brown fox jumps over the lazy dog";
        pd_shared3p xor_uint8[[1]] vec = kl_str(str);
        string sub_str = "k brown f";
        pd_shared3p xor_uint8[[1]] vec2 = kl_str(sub_str);
        string sub_str2 = "mps over th";
        pd_shared3p xor_uint8[[1]] vec3 = kl_str(sub_str2);
        test(test_prefix, declassify(kl_strContains(vec,vec2)) && declassify(kl_strContains(vec,vec3)));

        str = "The quick brown fox jumps over the lazy dog";
        vec = kl_str(str);
        sub_str = "The quic";
        vec2 = kl_str(sub_str);
        sub_str2 = "y dog";
        vec3 = kl_str(sub_str2);
        test(test_prefix, declassify(kl_strContains(vec,vec2)) && declassify(kl_strContains(vec,vec3)));
    }

    test_prefix = "Index of pattern in known string";
    {
        string str = "The quick brown fox jumps over the lazy dog";
        pd_shared3p xor_uint8[[1]] vec = kl_str(str);
        string sub_str = "ck brown fo";
        pd_shared3p xor_uint8[[1]] vec2 = kl_str(sub_str);
        string sub_str2 = "r the laz";
        pd_shared3p xor_uint8[[1]] vec3 = kl_str(sub_str2);
        pd_shared3p uint index = kl_strIndexOf(vec,vec2);
        pd_shared3p uint index2 = kl_strIndexOf(vec,vec3);
        test(test_prefix, declassify(index) == 7 && declassify(index2) == 29);
    }

    test_prefix = "String hamming test for known strings";
    {
        string str = "this is a test";
        pd_shared3p xor_uint8[[1]] vec = kl_str(str);
        string str2 = "this a test is";
        pd_shared3p xor_uint8[[1]] vec2 = kl_str(str2);
        pd_shared3p uint hammed = kl_strHamming(vec,vec2);
        test(test_prefix, declassify(hammed) == 8);

        str = "this is a test";
        vec = kl_str(str);
        str2 = "tset a si siht";
        vec2 = kl_str(str2);
        hammed = kl_strHamming(vec,vec2);
        test(test_prefix, declassify(hammed) == 10);
    }

    test_prefix = "Levenshtein distance for known string";
    {
        string str = "this is a test";
        string str2 = "these are two tests";
        pd_shared3p xor_uint8[[1]] vec = kl_str(str);
        pd_shared3p xor_uint8[[1]] vec2 = kl_str(str2);
        pd_shared3p uint distance = kl_strLevenshtein(vec,vec2);
        test(test_prefix, declassify(distance) == 9);
    }

    test_report();
}
