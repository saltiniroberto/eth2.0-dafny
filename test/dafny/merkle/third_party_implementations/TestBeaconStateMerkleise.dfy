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
 
include "../../../../src/dafny/utils/NativeTypes.dfy"
include "../../../../src/dafny/utils/Eth2Types.dfy"
include "../../../../src/dafny/utils/Helpers.dfy"
include "../../../../src/dafny/ssz/BytesAndBits.dfy"
include "../../../../src/dafny/ssz/BitListSeDes.dfy"
include "../../../../src/dafny/utils/DafTests.dfy"
include "../../test_utils/StringConversions.dfy"
include "../../../../src/dafny/merkle/Merkleise.dfy"
include "../../../../src/dafny/beacon/helpers/Crypto.dfy"
include "../../../lowlevel_modules/CommandLine.dfy"
include "ThirdPartyMerkleisation.dfy"
include "../../../lowlevel_modules/Rand.dfy"

datatype FailureReason = Limit | Content

lemma lemmaWellTypedBytes(r:Eth2Types.RawSerialisable)
requires r.Bytes?
requires |r.bs| > 0
ensures Eth2Types.wellTyped(r)
{ }

lemma lemmaWellTypedUint64(r:Eth2Types.RawSerialisable)
requires r.Uint64?
requires r.n < 0x10000000000000000
ensures Eth2Types.wellTyped(r)
{ }

lemma lemmaWellTypedBeaconBlockHeader(slot:Eth2Types.RawSerialisable, parent_root:Eth2Types.Bytes32, state_root:Eth2Types.Bytes32)
requires    Eth2Types.wellTypedContainerField(slot,Eth2Types.Uint64_)
ensures var bbh:= Eth2Types.BeaconBlockHeader(slot,parent_root,state_root);
            && Eth2Types.wellTypedContainer(bbh)
            && Eth2Types.wellTyped(bbh)
{ }

function method {:fuel Rand.Rand,0,0} getRandomBytes32(): Eth2Types.Bytes32 
{
    var bs := Helpers.initSeq<Eth2Types.byte>((x:nat) => (Rand.Rand()% 0x100) as Eth2Types.byte,32);
    assert |bs| == 32;
    var r := Eth2Types.Bytes(bs);
    lemmaWellTypedBytes(r);
    r
}


function method  {:fuel Eth2Types.wellTypedContainer,3} getRandomBeaconBlockHeader(): Eth2Types.BeaconBlockHeader
ensures getRandomBeaconBlockHeader().BeaconBlockHeader?
ensures Eth2Types.wellTyped(getRandomBeaconBlockHeader())
ensures Eth2Types.typeOf(getRandomBeaconBlockHeader()) == Eth2Types.BeaconBlockHeader_
{
    var slot := getRandomSlot();
    
    var bs1: Eth2Types.Bytes32 := getRandomBytes32();

    var bs2: Eth2Types.Bytes32 := getRandomBytes32();

    lemmaWellTypedBeaconBlockHeader(slot,bs1,bs2);

    Eth2Types.BeaconBlockHeader(
        slot,
        bs1,
        bs2
    )
}

function method {:fuel getRandomBytes32,0,0} getRandomRootVector(): Eth2Types.RawSerialisable
ensures Eth2Types.wellTypedContainerField(getRandomRootVector(), Eth2Types.Vector_(Eth2Types.Bytes_(32),Constants.SLOTS_PER_HISTORICAL_ROOT as nat));
{
    Eth2Types.Vector(getRandomRootSeq(Constants.SLOTS_PER_HISTORICAL_ROOT as nat))
}

function method {:fuel getRandomBytes32,0,0} getRandomRootSeq(n:nat): seq<Eth2Types.Bytes32>
ensures |getRandomRootSeq(n)| == n
ensures forall i | 0 <= i < |getRandomRootSeq(n)| :: Eth2Types.wellTyped(getRandomRootSeq(n)[i])
{
    if n == 0 then
        []
    else
        [getRandomBytes32()] + getRandomRootSeq(n-1)
}

function method {:fuel Rand.Rand,0,0} getRandomSlot(): Eth2Types.RawSerialisable
ensures Eth2Types.wellTypedContainerField(getRandomSlot(),Eth2Types.Uint64_);
{
    Eth2Types.Uint64(Rand.Rand() % 0x10000000000000000)
}

/**
 * Returns a random sequence of Uint64 of size between 0 and 2000-1
 */
function method {:fuel getRandomBytes32,0,0} {:fuel Rand.Rand,0,0} getRandomBeaconState(): Eth2Types.BeaconState
{
    var slot := getRandomSlot();

    var bbh  :=  getRandomBeaconBlockHeader();

    var block_roots := getRandomRootVector();
  
    var state_roots := getRandomRootVector();

    Eth2Types.BeaconState(
        slot,
        bbh,
        block_roots,
        state_roots
    )
}

function method castToUint64(n:nat): Eth2Types.RawSerialisable
requires n < 0x10000000000000000
ensures castToUint64(n).Uint64?
ensures Eth2Types.wellTypedContainerField(castToUint64(n),Eth2Types.Uint64_);
{
    var r:= Eth2Types.Uint64(n);
    lemmaWellTypedUint64(r);
    r
}

/**
 * @param s List
 *
 * @returns True iff the hash tree root calculated by the third party
 * markleisation function matches the value returned by the Dafny
 * correct-by-construction merkleisation function
 */
predicate method verifyBeaconState(s: Eth2Types.BeaconState, failPercentage: nat)
requires s.BeaconState?
requires Eth2Types.wellTypedContainer(s)
{
    var dfyHashRoot := SSZ_Merkleise.getHashTreeRoot(s);

    var ThirdPartyBeaconState: Eth2Types.BeaconState :=    
                                if s.slot.n >= 0x10000000000000000 * (100 - failPercentage) /100 then
                                    var newS := castToUint64((s.slot.n+1) % 0x10000000000000000);                                    
                                    var s:=
                                    Eth2Types.BeaconState(
                                        newS,
                                        s.latest_block_header,
                                        s.block_roots,
                                        s.state_roots
                                    );
                                    assert Eth2Types.wellTypedContainer(s);
                                    s
                                    
                                else
                                    s
                                ;

    var ThirdParthyHash := ThirdPartyMerkleisation.BeaconStateRoot(ThirdPartyBeaconState);

    dfyHashRoot == ThirdParthyHash
}

/**
 * @param numTests Number of test items to create
 * 
 * @returns A sequence of randomly generated test items
 */
function method CompileRecTest(numTests:nat, percFailure:nat) :seq<DafTest.TestItem>
requires 0 <= percFailure <= 100
ensures |CompileRecTest(numTests,percFailure)| == numTests
{
    if numTests == 0 then
        []
    else
        [createTestItem(getRandomBeaconState(),percFailure)] +
        CompileRecTest(numTests-1,percFailure)
}

function method createTestItem(s: Eth2Types.BeaconState, percFailure: nat): DafTest.TestItem
requires s.BeaconState?
requires Eth2Types.wellTypedContainer(s)
{
    DafTest.TestItem(
                "Test\n" +
                 StringConversions.join(StringConversions.ByteSeqToHexSeqCompressed(SSZ_Merkleise.getHashTreeRoot(s))," ")
            ,
                () => verifyBeaconState(s,percFailure)
    )
}

/**
 * @param args Command line arguments
 * 
 * @returns true iff the command line arguments are well formed
 */
predicate method correctInputParameters(args: seq<string>)
{
    && |args| == 3
    && StringConversions.isNumber(args[1])
    && StringConversions.isNumber(args[2])
    && 0 <= StringConversions.atoi(args[2]) <= 100
}

/**
 * Execution Entry Point
 */
method Main()
{
    var args := GetCommandLineParamters();

    if(correctInputParameters(args))
    {
        var numTests := StringConversions.atoi(args[1]);
        var percFailure := StringConversions.atoi(args[2]);

        var fixedTest := [];

        var tests :=    fixedTest +
                        CompileRecTest(numTests,percFailure);


        var merkleTestSuite := DafTest.TestSuite("List Merkleisation",tests[..numTests]);

        DafTest.executeTests(merkleTestSuite);
    }
    else
    {
        print "First argument must be a natural number indicating the number of tests.\n";
        print "The second argument must be a natural number between 0 and 100 (included) which specifies the average percentage of tests that should fail.\n";
        print "The third argument must be either the string \"content\" or the string \"limit\". "+
              "This argument indicates whether the tests expected to fail should fail because of a variation in the list content or in the list limit.\n";
    }
}

/**
 * This is just to ensure the tye "mycrypto" module is reference otherwise the
 * Go compiler throws an error
 */
method dummy_method()
{
    var dummy := Crypto.hash([]);
}