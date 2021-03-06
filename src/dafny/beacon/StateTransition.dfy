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
include "../utils/Eth2Types.dfy"
include "../utils/Helpers.dfy"
include "../ssz/Constants.dfy"
include "BeaconChain.dfy"
include "Validators.dfy"

/**
 * State transition function for the Beacon Chain.
 */
module StateTransition {
    
    //  Import some constants, types and beacon chain helpers.
    import opened NativeTypes
    import opened Eth2Types
    import opened Constants
    import opened BeaconChain
    import opened Validators
    import opened Helpers

    /** The default zeroed Bytes32.  */
    const SEQ_EMPTY_32_BYTES := timeSeq<byte>(0,32)
    
    /**
     *  The default (empty) Bytes32
     */
    const EMPTY_BYTES32 : Bytes32 := Bytes(SEQ_EMPTY_32_BYTES)

    /** The historical roots type.  */
    type VectorOfHistRoots = x : seq<Bytes32> |  |x| == SLOTS_PER_HISTORICAL_ROOT as int
        witness EMPTY_HIST_ROOTS

    /** Empty vector of historical roots. */
    const EMPTY_HIST_ROOTS := timeSeq<Bytes32>(EMPTY_BYTES32, SLOTS_PER_HISTORICAL_ROOT as int)

    /**
     *  Compute Root/Hash/Bytes32 for different types.
     *  
     *  @todo   Use the hash_tree_root from Merkle?.
     *  @note   The property of hash_tree_root below is enough for 
     *          proving some invariants. So we may use a module refinement
     *          to integrate the actual hash_tree_root from Merkle module.
     */
    function method hash_tree_root<T(==)>(t : T) : Bytes32 
        ensures hash_tree_root(t) != EMPTY_BYTES32

    /** Collision free hash function. 
     *  
     *  @note   This does not seem to affect the proofs so far, so
     *          this lemma is commented out, but left in the code
     *          for future reference.
     **/
    // lemma {:axiom} foo<T(==)>(t1: T, t2: T) 
        // ensures t1 == t2 <==> hash_tree_root(t1) == hash_tree_root(t2)

    /** 
     *  The Beacon state type.
     *
     *  @link{https://notes.ethereum.org/@djrtwo/Bkn3zpwxB?type=view} 
     *  The beacon chain’s state (BeaconState) is the core object around 
     *  which the specification is built. The BeaconState encapsulates 
     *  all of the information pertaining to: 
     *      - who the validators are, 
     *      - in what state each of them is in, 
     *      - which chain in the block tree this state belongs to, and 
     *      - a hash-reference to the Ethereum 1 chain.
     *
     *  Beginning with the genesis state, the post state of a block is considered valid if it passes all of 
     *  the guards within the state transition function. Thus, the precondition of a block is recursively defined as 
     *  being a valid postcondition of running  the state transition function on the previous block and its state 
     *  all the way back to the genesis state.
     *
     * @param   slot                            Time is divided into “slots” of fixed length at which actions occur 
     *                                          and state transitions happen. This field tracks the slot of the containing
     *                                          state, not necessarily the slot according to the local wall clock.
     *
     * @param   latest_block_header             The latest block header seen in the chain defining this state. This *                                          blockheader has During the slot transition of the block, the header is
     *                                           stored without the real state root but instead with a stub of Root
     *                                          () (empty 0x00 bytes). At the start of the next slot transition before
     *                                          anything has been modified within state, the state root is calculated and
     *                                          added to the latest_block_header. This is done to eliminate the circular 
     *                                          dependency of the state root being embedded in the block header.
     *
     * @param   block_roots                     Per-slot store of the recent block roots.The block root for a slot is 
     *                                          added at the start of the next slot to avoid the circular dependency due 
     *                                          to the state root being embedded in the block. For slots that are skipped 
     *                                          (no block in the chain for the given slot), the most recent block root in 
     *                                          the chain prior to the current slot is stored for the skipped slot. When 
     *                                          validators attest to a given slot, they use this store of block roots as 
     *                                          an information source to cast their vote.
     *
     * @param   state_roots                     Per-slot store of the recent state roots.The state root for a slot is 
     *                                          stored at the start of the next slot to avoid a circular dependency.
     *
     * @param   eth1_deposit_index              Index of the next deposit to be processed. Deposits must be added to the 
     *                                          next block and processed if state.eth1_data.deposit_count > 
     *                                          state.eth1_deposit_index
     *
     * @param   validators                      List of Validator records, tracking the current full registry. Each 
     *                                          validator contains  relevant data such as pubkey, withdrawal credentials,
     *                                          effective balance, a slashed  boolean, and status (pending, active, 
     *                                          exited, etc)
     *
     * @note                                    Some fields are not integrated yet but a complete def can be found in 
     *                                          the archive branch.
     */
    datatype BeaconState = BeaconState(
        slot: Slot,
        latest_block_header: BeaconBlockHeader,
        block_roots: VectorOfHistRoots,
        state_roots: VectorOfHistRoots,
        eth1_deposit_index : uint64,
        validators: seq<Validator>
    )

    /**
     *  Whether a block is valid in a given state.
     *
     *  @param  s   A beacon state.
     *  @param  b   A block.
     *
     *  @returns    true iff `b` can be successfully added to the state `s`.
     */
    predicate isValid(s : BeaconState, b : BeaconBlock) 
    {
        //  block slot should be in the future.
        s.slot < b.slot 
        //  Fast forward s to b.slot and check `b` can be attached to the
        //  resulting state's latest_block_header.
        && b.parent_root == 
            hash_tree_root(
                forwardStateToSlot(resolveStateRoot(s), 
                b.slot
            ).latest_block_header) 
        //  Check that number of deposits in b.body can be processed
        && s.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000  
        //  Check that the block provides the correct hash for the state.
        &&  b.state_root == hash_tree_root(
                updateDeposits(
                    addBlockToState(
                        forwardStateToSlot(resolveStateRoot(s), b.slot), 
                        b
                    ),
                    b
                )
            )
    }

    /**
     *  Compute the state obtained after adding a block.
     *  
     *  @param      s   A beacon state.
     *  @param      b   A block.
     *  @returns        The state obtained after adding `b` to the current state.
     *                  
     */
     method stateTransition(s: BeaconState, b: BeaconBlock) returns (s' : BeaconState)
        //  make sure the last state was one right after addition of new block
        requires isValid(s, b)

        requires s.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000  

        /** The next state latest_block_header is same as b except for state_root that is 0. */
        ensures s'.latest_block_header == BeaconBlockHeader(b.slot, b.parent_root, EMPTY_BYTES32)
        /** s' slot is now adjusted to the slot of b. */
        ensures s'.slot == b.slot
        /** s' parent_root is the hash of the state obtained by resolving/forwarding s to
            the slot of b.  */
        ensures s'.latest_block_header.parent_root  == 
            hash_tree_root(
                forwardStateToSlot(resolveStateRoot(s), b.slot)
                .latest_block_header
            )
        ensures s'.eth1_deposit_index as int == s.eth1_deposit_index as int + |b.body.deposits|
    {
        //  finalise slots before b.slot.
        var s1 := processSlots(s, b.slot);

        //  Process block and compute the new state.
        s' := processBlock(s1, b);  

        // Verify state root (from eth2.0 specs)
        // A proof that this function is correct establishes that this assert statement 
        // is never violated (i.e. when isValid() is true.)
        // In the Eth2.0 specs this check is conditional and enabled by default.
        //  if validate_result:
        assert (b.state_root == hash_tree_root(s'));
    }  

    /**
     *  Advance current state to a given slot.
     *
     *  This mainly consists in advancing the slot number to
     *  a target future `slot` number and updating/recording the history of intermediate
     *  states (and block headers). 
     *  Under normal circumstances, where a block is received at each slot,
     *  this involves only one iteration of the loop.
     *  Otherwise, the first iteration of the loop `finalises` the block header
     *  of the previous slot before recortding it, 
     *  and subsequent rounds advance the slot number and record the history of states
     *  and blocks for each slot.
     *
     *  @param  s       A state
     *  @param  slot    The slot to advance to. This is usually the slot of newly
     *                  proposed block.
     *  @returns        The state obtained after advancing the histories to slot.
     *      
     *  @note           The specs have the the first processSlot integrated in the while loop. However, 
     *                  because s.slot < slot, the while bdoy must be executed at least one time.
     *                  To simplify the proof, we have taken this first iteration outside of the loop. It does 
     *                  not change the semantics but enables us to use the state obtained after the first
     *                  iteration the loop and prove it is the same as resolveStateRoot(s).
     *
     */
    method processSlots(s: BeaconState, slot: Slot) returns (s' : BeaconState)
        requires s.slot < slot  //  update in 0.12.0 (was <= before)

        ensures s' == forwardStateToSlot( resolveStateRoot(s), slot)
        ensures s.latest_block_header.parent_root == s'.latest_block_header.parent_root  
        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        
        //  Termination ranking function
        decreases slot - s.slot
    {
        //  Start from the current state and update it with processSlot.
        //  First iteration of the loop in process_slots (Eth2)
        s' := processSlot(s);
        s':= s'.(slot := s'.slot + 1) ;
        //  The following asserts are not needed for the proof but provided for readability. 
        assert(s' == resolveStateRoot(s));  
        //  s'.block header state_root should now be resolved
        assert(s'.latest_block_header.state_root != EMPTY_BYTES32);

        //  Now fast forward to slot
        //  Next iterations of process_slot (Eth2)
        while (s'.slot < slot)  
            invariant s'.slot <= slot
            invariant s'.latest_block_header.state_root != EMPTY_BYTES32
            invariant s' == forwardStateToSlot(resolveStateRoot(s), s'.slot) // Inv1
            invariant s'.eth1_deposit_index == s.eth1_deposit_index
            decreases slot - s'.slot 

        {
            s':= processSlot(s');
            //  Process epoch on the start slot of the next epoch
            if (s'.slot + 1) % SLOTS_PER_EPOCH  == 0 {
                s' := processEpoch(s');
            }
            //  s'.slot is now processed: history updated and block header resolved
            //  The state's slot is processed and we can advance to the next slot.
            s':= s'.(slot := s'.slot + 1) ;
        }
    }

    /** 
     *  Cache data for a slot.
     *
     *  This function also finalises the block header of the last block
     *  so that it records the hash of the state `s`. 
     *
     *  @param  s   A state.
     *  @returns    A new state where `s` has been added/cached to the history and
     *              the block header tracks the hash of the most recent received
     *              block.
     *
     *  @note       This function method could be a method (as per the Eth2 specs).
     *              However, this requires to expose the properties of the computation
     *              as methods are not inlined. 
     *  @note       Matches eth2.0 specs, need to uncomment update of state/block_roots.
     *
     *  @todo       Make this a method to have a def closer to Eth2 implementation.  
     */
    method processSlot(s: BeaconState) returns (s' : BeaconState)
        requires s.slot as nat + 1 < 0x10000000000000000 as nat

        ensures  s.latest_block_header.state_root == EMPTY_BYTES32 ==>
            s' == resolveStateRoot(s).(slot := s.slot)
        ensures  s.latest_block_header.state_root != EMPTY_BYTES32 ==>
            s' == nextSlot(s).(slot := s.slot)
        ensures s.latest_block_header.parent_root == s'.latest_block_header.parent_root
        ensures s'.eth1_deposit_index == s'.eth1_deposit_index
    {
        s' := s;

        //  Cache state root. Record the hash of the previous state in the history.
        var previous_state_root := hash_tree_root(s); 

        s' := s'.(state_roots := s'.state_roots[(s'.slot % SLOTS_PER_HISTORICAL_ROOT) as int := previous_state_root]);

        //  Cache latest block header state root
        if (s'.latest_block_header.state_root == EMPTY_BYTES32) {
            s' := s'.(latest_block_header := s'.latest_block_header.(state_root := previous_state_root));
        }

        //  Cache block root
        var previous_block_root := hash_tree_root(s'.latest_block_header);

        //  Compute the final value of the new state.
        s' := s'.(block_roots := s'.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := previous_block_root]);
    }

    /**
     *  Verify that a block is valid.
     *  
     *  @param      s   A beacon state.   
     *  @param      b   A block header.
     *  @returns        The state obtained after processing `b`.
     *
     *  @note   Matches eth2.0 specs, need to implement randao, eth1, operations. 
     */
     method processBlock(s: BeaconState, b: BeaconBlock) returns (s' : BeaconState) 
        requires b.slot == s.slot
        requires b.parent_root == hash_tree_root(s.latest_block_header)
        requires s.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000  

        ensures s' == updateDeposits(addBlockToState(s, b), b)
    {
        //  Start by creating a block header from the ther actual block.
        s' := processBlockHeader(s, b); 
        
        //  process_randao(s, b.body)
        //  process_eth1_data(s, b.body)
        s' := process_operations(s', b.body);
    }

    /**
     *  Check whether a block is valid and prepare and initialise new state
     *  with a corresponding block header. 
     *
     *  @param  s   A beacon state.
     *  @param  b   A block.
     *  @returns    The state obtained processing the block.
     *
     *  @note   Matches eth2.0 specs except proposer slashing verification.
     */
    method processBlockHeader(s: BeaconState, b: BeaconBlock) returns (s' : BeaconState) 
        //  Verify that the slots match
        requires b.slot == s.slot  
        // Verify that the parent matches
        requires b.parent_root == hash_tree_root(s.latest_block_header) 

        requires s.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000 


        ensures s' == addBlockToState(s, b)
    {
        s':= s.(
            latest_block_header := BeaconBlockHeader(
                b.slot,
                b.parent_root,
                EMPTY_BYTES32
            )
        );
    }
    
    /**
     *  At epoch boundaries, update justifications, rewards, penalities,
     *  resgistry, slashing, and final updates.
     *
     *  @param  s   A beacon state.
     *  @returns    
     *  @todo       To be specified and implemented. currently returns s.
     */
    method processEpoch(s: BeaconState) returns (s' : BeaconState) 
        ensures s' == s
    {
        return s;
    }

    /**
     *  Process the operations defined by a block body.
     *  
     *  @param  s   A state.
     *  @param  bb  A block body.
     *  @returns    The state obtained after applying the operations of `bb` to `s`.
     */
    method process_operations(s: BeaconState, bb: BeaconBlockBody)  returns (s' : BeaconState)  
        requires s.eth1_deposit_index as int + |bb.deposits| < 0x10000000000000000 
        ensures s' == s.(eth1_deposit_index := (s. eth1_deposit_index as int + |bb.deposits|) as uint64 )
    {
        //  process deposits in the beacon block body.
        s' := s;

        var i := 0; 
        while i < |bb.deposits| 
            invariant s.eth1_deposit_index as int + i <  0x10000000000000000 
            invariant i <= |bb.deposits|
            invariant s' == s.(eth1_deposit_index := s.eth1_deposit_index as int + i) ;  
        {
            s':= process_deposit(s', bb.deposits[i]);
            i := i + 1;
        }
    }

    /**
     *  Process a deposit operation.
     *
     *  @param  s   A state.
     *  @param  d   A deposit.  
     *  @returns    The state obtained depositing of `d` to `s`.
     */
    method process_deposit(s: BeaconState, d : Deposit)  returns (s' : BeaconState)  
        requires s. eth1_deposit_index as int + 1 < 0x10000000000000000 
        ensures s' == s.(eth1_deposit_index := s. eth1_deposit_index + 1)
    {
        s' := s;
        //  Verify the Merkle branch
        // assert is_valid_merkle_branch(
        //     leaf=hash_tree_root(deposit.data),
        //     branch=deposit.proof,
        //     depth=DEPOSIT_CONTRACT_TREE_DEPTH + 1,  # Add 1 for the List length mix-in
        //     index=state.eth1_deposit_index,
        //     root=state.eth1_data.deposit_root,
        // );
        //  Deposits must be processed in order
        s' := s.(eth1_deposit_index := s. eth1_deposit_index + 1);

        // pubkey = deposit.data.pubkey
        // amount = deposit.data.amount
        // validator_pubkeys = [v.pubkey for v in state.validators]
        // if pubkey not in validator_pubkeys:
        //     # Verify the deposit signature (proof of possession) which is not checked by the deposit contract
        //     deposit_message = DepositMessage(
        //         pubkey=deposit.data.pubkey,
        //         withdrawal_credentials=deposit.data.withdrawal_credentials,
        //         amount=deposit.data.amount,
        //     )
        //     domain = compute_domain(DOMAIN_DEPOSIT)  # Fork-agnostic domain since deposits are valid across forks
        //     signing_root = compute_signing_root(deposit_message, domain)
        //     if not bls.Verify(pubkey, signing_root, deposit.data.signature):
        //         return

        //     # Add validator and balance entries
        //     state.validators.append(get_validator_from_deposit(state, deposit))
        //     state.balances.append(amount)
        // else:
        //     # Increase balance by deposit amount
        //     index = ValidatorIndex(validator_pubkeys.index(pubkey))
            // increase_balance(state, index, amount)

        //  Simplified version assuming the validator is already in state.validators (else section above)
        //  Increase balance by deposit amount
        // var index := ValidatorIndex(validator_pubkeys.index(pubkey))
        // increase_balance(state, index, amount);
        return s';
    }


    /**
     *  Collect oubkey in a list of validators.
     *
     *  @param  xv  A list of validators,
     *  @returns    The set of keys helpd byt the validators in `xv`.
     */
    function keysInValidators(xv : seq<Validator>) : set<BLSPubkey>
    {
        if |xv| == 0 then  
            {}
        else 
            { xv[0].pubkey } + keysInValidators(xv[1..])
    }


    //  Specifications of finalisation of a state and forward to future slot.

    /**
     *  Result of processing a block.
     *  
     *  @param  s   A state.
     *  @param  b   A block to add to the state `s`.
     *  @returns    The state `s` updated to point to `b` with state_root set to 0.
     */
    function addBlockToState(s: BeaconState, b: BeaconBlock) :  BeaconState 
        //  Verify that the slots match
        requires b.slot == s.slot  
        // Verify that the parent matches
        requires b.parent_root == hash_tree_root(s.latest_block_header) 
    {
        s.(
            latest_block_header := BeaconBlockHeader(
                b.slot,
                b.parent_root,
                EMPTY_BYTES32
            )
        )
    }

    /**
     *  Complete the current slot.
     *
     *  @param  s   A beacon state.
     *  @returns    A new state `s' such that:
     *              1. a new latest_block_header' state_root set to the hash_tree_root(s) 
     *              2. the hash_tree_root(s) archived in the s'.state_roots for the slot
     *              3. the hash_tree_root of the new_block_header is archived 
     *              in s'.block_roots
     */
    function resolveStateRoot(s: BeaconState): BeaconState 
        //  Make sure s.slot does not  overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        //  parent_root of the state block header is preserved
        ensures s.latest_block_header.parent_root == resolveStateRoot(s).latest_block_header.parent_root
        //  eth1_deposit_index is left unchanged
        ensures s.eth1_deposit_index == resolveStateRoot(s).eth1_deposit_index
    {
        var new_latest_block_header := 
            if (s.latest_block_header.state_root == EMPTY_BYTES32 ) then 
                s.latest_block_header.(state_root := hash_tree_root(s))
            else 
                s.latest_block_header
            ;
        
        BeaconState(
            // slot unchanged
            s.slot + 1,
            new_latest_block_header,
            //  add new block_header root to block_roots history.
            s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(new_latest_block_header)],
            //  add previous state root to state_roots history
            s.state_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s)],
            s.eth1_deposit_index,
            s.validators
        )
    }

    /**
     *  Finalise a state and forward to slot in the future.
     *  
     *  @param  s       A state
     *  @param  slot    A slot. 
     *  @returns        A new state obtained by  archiving roots and incrementing slot.
     *                  slot.
     */
    function forwardStateToSlot(s: BeaconState, slot: Slot) : BeaconState 
        requires s.slot <= slot

        ensures forwardStateToSlot(s, slot).slot == slot
        ensures forwardStateToSlot(s, slot).latest_block_header ==  s.latest_block_header
        ensures forwardStateToSlot(s, slot).eth1_deposit_index == s.eth1_deposit_index
        //  termination ranking function
        decreases slot - s.slot
    {
        if (s.slot == slot) then 
            s
        else
            nextSlot(forwardStateToSlot(s, slot - 1))
    }

    /**
     *  Advance a state by one slot.
     *
     *  @param  s   A beacon state.
     *  @returns    The successor state for `slot + 1`.
     *
     *  @note       This function increment the slot number and archives 
     *              the previous state_root and block_root, and copy verbatim the 
     *              latest_block_header.
     */
    function nextSlot(s : BeaconState) : BeaconState 
        //  Make sure s.slot does not overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
    {
        //  Add header root to history of block_roots
        var new_block_roots := s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s.latest_block_header)];
        //  Add state root to history of state roots
        var new_state_roots := s.state_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s)];
        //  Increment slot and copy latest_block_header
        s.(
            slot := s.slot + 1,
            block_roots := new_block_roots,
            state_roots := new_state_roots
        )
    }

     /**
     *  Take into account deposits in a block.
     *
     *  @param  s       A beacon state.
     *  @param  body    A block body.
     *  @returns        The state obtained after taking account the deposits in `body` from state `s` 
     */
    function updateDeposits(s: BeaconState, b: BeaconBlock) : BeaconState 
        requires s.eth1_deposit_index as int +  |b.body.deposits| < 0x10000000000000000 
    {
        s.(
            eth1_deposit_index := (s.eth1_deposit_index as int + |b.body.deposits|) as uint64
        )
    }


}