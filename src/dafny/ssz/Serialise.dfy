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
include "../utils/Helpers.dfy"
include "IntSeDes.dfy"
include "BoolSeDes.dfy"
include "BitListSeDes.dfy"
include "../utils/MathHelpers.dfy"
include "../libraries/integers/power.i.dfy"

/**
 *  SSZ library.
 *
 *  Serialise, deserialise
 */
module SSZ {

    import opened NativeTypes
    import opened NonNativeTypes
    import opened Eth2Types
    import opened IntSeDes
    import opened BoolSeDes
    import opened BitListSeDes
    import opened Helpers
    import opened MathHelpers
    import opened Math__power_i
    import opened Math__power_s    

    /** SizeOf.
     *
     *  @param  s   A serialisable object of type uintN or bool.
     *  @returns    The number of bytes used by a serialised form of this type.
     *
     *  @note       This function needs only to be defined for basic types
     *              i.e. uintN or bool.
     */
    function method sizeOf(s: Serialisable): nat
        requires typeOf(s) in {Bool_, Uint64_}
        ensures 1 <= sizeOf(s) <= 32
        ensures sizeOf(s) == |serialise(s)|
    {
        match s
            case Bool(_) => 1

            case Uint64(_) => 8
    }

    /** default.
     *
     *  @param  t   Serialisable tipe.
     *  @returns    The default serialisable for this tipe.
     *
    */
    function method default(t : Tipe) : Serialisable 
    requires t in {Bool_, Uint64_, Bitlist_,Bytes32_}
    {
            match t 
                case Bool_ => Bool(false)

                case Uint64_ => Uint64(0)              

                case Bitlist_ => Bitlist([])

                case Bytes32_ => Bytes32(timeSeq(0,32))
    }

    /** Serialise.
     *
     *  @param  s   The object to serialise.
     *  @returns    A sequence of bytes encoding `s`.
     */
    function method serialise(s : Serialisable) : seq<byte> 
    requires typeOf(s) in {Bool_, Uint64_, Bitlist_, Bytes32_}
    {
        match s
            case Bool(b) => boolToBytes(b)

            case Uint64(n) =>   reveal_power();
                                int_to_bytes(s.n64 as nat, 8)  

            case Bitlist(xl) => fromBitlistToBytes(xl)

            case Bytes32(bs) => bs
    }

    /** Deserialise. 
     *  
     *  @param  xs  A sequence of bytes.
     *  @param  s   A target type for the deserialised object.
     *  @returns    Either a Success if `xs` could be deserialised
     *              in an object of type s or a Failure oytherwise.
     *  
     *  @note       It would probabaly be good to return the suffix of `xs`
     *              that has not been used in the deserialisation as well.
     */
    function method deserialise(xs : seq<byte>, s : Tipe) : Try<Serialisable>
    requires s in {Bool_, Uint64_, Bitlist_,Bytes32_}
    {
        match s
            case Bool_ => if |xs| == 1 then
                                Success(Bool(byteToBool(xs[0])))
                            else 
                                Failure

            case Uint64_ =>   if |xs|  == sizeOf(default(s)) then
                                Success(Uint64(bytes_to_int(xs) as uint64))
                            else 
                                Failure                                                                                                                    
                                
            case Bitlist_ => if (|xs| >= 1 && xs[|xs| - 1] >= 1) then
                                Success(Bitlist(fromBytesToBitList(xs)))
                            else
                                Failure

            case Bytes32_ => if |xs| == 32 then
                                Success(Bytes32(xs))
                            else Failure
    }

    //  Specifications and Proofs
    
    /** 
     * Well typed deserialisation does not fail. 
     */
    lemma wellTypedDoesNotFail(s : Serialisable) 
    requires typeOf(s) in {Bool_, Uint64_, Bitlist_,Bytes32_}
        ensures deserialise(serialise(s), typeOf(s)) != Failure 
    {   //  Thanks Dafny.
    }

    /** 
     * Deserialise(serialise(-)) = Identity for well typed objects.
     */
    lemma seDesInvolutive(s : Serialisable) 
        requires typeOf(s) in {Bool_, Uint64_, Bitlist_,Bytes32_}
        ensures deserialise(serialise(s), typeOf(s)) == Success(s) 
        {   //  thanks Dafny.
            match s 
                case Bitlist(xl) => 
                    calc {
                        deserialise(serialise(s), typeOf(s));
                        ==
                        deserialise(serialise(Bitlist(xl)), Bitlist_);
                        == 
                        deserialise(fromBitlistToBytes(xl), Bitlist_);
                        == 
                        Success(Bitlist(fromBytesToBitList(fromBitlistToBytes(xl))));
                        == { bitlistDecodeEncodeIsIdentity(xl); } 
                        Success(Bitlist(xl));
                    }

                case Bool(_) =>  //  Thanks Dafny

                case Uint64(n) =>   reveal_power();
                                    lemmaBytesToIntIsTheInverseOfIntToBytes(s.n64 as nat,8);

                case Bytes32(_) => // Thanks Dafny
            
        }

    /**
     *  Serialise is injective.
     */
    lemma {:induction s1, s2} serialiseIsInjective(s1: Serialisable, s2 : Serialisable)
        requires typeOf(s1) in {Bool_, Uint64_, Bitlist_,Bytes32_}
        ensures typeOf(s1) == typeOf(s2) ==> 
                    serialise(s1) == serialise(s2) ==> s1 == s2 
    {
        //  The proof follows from involution
        if ( typeOf(s1) ==  typeOf(s2)) {
            if ( serialise(s1) == serialise(s2) ) {
                //  Show that success(s1) == success(s2) which implies s1 == s2
                calc {
                    Success(s1) ;
                    == { seDesInvolutive(s1); }
                    deserialise(serialise(s1), typeOf(s1));
                    ==
                    deserialise(serialise(s2), typeOf(s2));
                    == { seDesInvolutive(s2); }
                    Success(s2);
                }
            }
        }
    }
}