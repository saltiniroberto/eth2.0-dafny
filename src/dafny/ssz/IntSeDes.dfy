/*
 * Copyright 2020 ConsenSys AG.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may 
 * not use this file except in compliance with the License. You may obtain 
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
 * License for the specific language governing permissions and limitations 
 * under the License.
 */

include "../utils/NativeTypes.dfy"
include "../utils/NonNativeTypes.dfy"
include "../utils/Eth2Types.dfy"
include "../utils/MathHelpers.dfy"
include "../libraries/integers/power.i.dfy"

/**
 *  Integers serialisation, desrialisation.
 *
 */
module IntSeDes {

    import opened NativeTypes
    import opened NonNativeTypes
    import opened Eth2Types
    import opened MathHelpers
    import opened Math__power_i
    import opened Math__power_s

    //  Uintk serialisation and deserielisation.
      
    /**
     * Computes the little endian serialisation of a natural value
     *
     * @param n        The value to serialise
     * @param length   Length of the serialisation.
     * @requires       n < power(0x100,length) 
     *
     * @returns        The `length`-byte little endian serialisation of `n`
     *
     */
    function method int_to_bytes(n: nat, length: nat) : bytes
    requires n as nat < power(0x100, length)
    ensures |int_to_bytes(n,length)| == length as int
    {
        reveal_power();
        if(length == 0) then
            []
        else
            [(n % 0x100) as uint8] +
            int_to_bytes(n / 0x100, length-1)
    }

    /**
     * Deserialise a sequence of bytes to a natural number using little endian
     * interpretation
     *
     * @param s Sequence of bytes. Must be no longer than 8 bytes.
     *
     * @returns The natural value corresponding to the little endian
     * deserialisation of `s`
     */
    function method bytes_to_int(s: bytes):nat
    ensures bytes_to_int(s)  < power(0x100, |s|)
    {
        reveal_power();
        if(|s| == 0) then
            0
        else
            s[0] as nat + bytes_to_int(s[1..])*0x100
    }

    /** `bytes_to_int` is the inverse of `int_to_bytes` */
    lemma lemmaBytesToIntIsTheInverseOfIntToBytes(n: nat, length: nat)
    requires int_to_bytes.requires(n,length)
    ensures bytes_to_int(int_to_bytes(n,length)) == n 
    { // Thanks Dafny
    }

    /** `int_to_bytes` is the inverse of `bytes_to_int` */
    lemma lemmaIntToBytesIsTheInverseOfBytesToInt(s: bytes)
    requires bytes_to_int.requires(s)
    ensures int_to_bytes(bytes_to_int(s),|s|) == s 
    { 
        if(|s|==0)
        {
            // Thanks Dafny
        }
        else
        {
            calc == {
                int_to_bytes(bytes_to_int(s),|s|);
                int_to_bytes(s[0] as nat + bytes_to_int(s[1..])*0x100,|s|);
                [s[0]] + int_to_bytes(bytes_to_int(s[1..]),(|s|-1));
                // via induction
                [s[0]] + s[1..];
                s;
            }
        }
    }     

}