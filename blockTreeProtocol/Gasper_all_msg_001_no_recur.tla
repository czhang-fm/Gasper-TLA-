-------------------- MODULE Gasper_all_msg_001_no_recur ---------------------------
(*
 A TLA+ specification of a simplified Ethereum consensus. 
 The simplifications are as follows:
 
 - The protocol runs for a fixed number of epochs, with a fixed set of validators

 - All validators have an equal weight

 - All blocks are generated at the beginning and known to all validators (!!!)

 - All attestations are decided at the beginning of a protocol execution, 
   satisfing some constraints.

 - Asynchronous channels are modelled by gradually and nondeterministically releasing 
   a subset of all attestations which are time-stamped to be less than or equal to the 
   current slot, received honest validators.

 - We define a super set of all possible behaviour of honest validators. Dishonest 
   validators are unconstrained. All behaviours are encoded in the initial set of
   FFG attestations. *** We do not consider HLMD Ghost at this stage ***

 - We focus on the safety property only: for any honest validators v1 and v2, the 
   most recent finalized block must be compatible (i.e., they are the same block, 
   or one block is an ancestor of the other)

   #DDS Dependable Distributed Systems, Consensys Software, 2023.
 *)
       
EXTENDS Integers, FiniteSets, Apalache

CONSTANTS 
    \* @type: Int;
    Honest,        \* number of honest validators
    \* @type: Int;
    Byzantine,     \* number of byzantine validators
    \* @type: Set(Str);
    HValidators,
    \* @type: Set(Str);
    BValidators,
    \* @type: Int;
    NumEpoch,      \* total number of epochs
    \* @type: Int;
    SlotPerEpoch   \* number of slots per epoch

(****************** DEFINITIONS *******************************)

MaxSlot == NumEpoch * SlotPerEpoch
Slots == 1..MaxSlot
GENESIS == 0       \* the first block/slot
Blocks == 0..MaxSlot  \* a block index corresponds to its slot index, except GENESIS = 0
NilBlock == -1     \* the parent of the GENESIS block or used for a block missing for a slot
Validators == HValidators \union BValidators
NumValidators == Honest + Byzantine
ValidatorPerSlot == NumValidators \div SlotPerEpoch \* integer division, to check later
Epochs == 0..NumEpoch  \* epoch 0 is reserved for GENESIS block
THRESHOLD == Byzantine * 2 + 1
BVotesLimit == Byzantine * NumEpoch \* was *2

(***************** STATE VARIABLES **********************************)
(* In this new version, we merge the fields slot and dst in an attestation record *)
VARIABLES
    \* @type: Int -> Int;
    blockTree,
    \* @type: Set({id: Str, src: Int, dst: Int});
    honestVotes,
    \* @type: Set({id: Str, src: Int, dst: Int});
    byzantineVotes,
    \* @type: Set({id: Str, src: Int, dst: Int});
    ffgVotes,      \* a set of FFG votes of record type [id: Str, slot, src: Epoch, dst: Block]
    \* @type: Int;
    currentSlot,
    \* @type: Str -> Set({id: Str, src: Int, dst: Int});
    receivedAttestations, \* a function mapping an honest validator to attestations(slots) that he has received so far
    \* @type: Str -> Set(Int);
    justifiedBlocks, \* a function mapping an honest validator to a set of justified blocks
    \* @type: Str -> Set(Int);
    finalizedBlocks, \* a function mapping an honest validator to a set of finalized blocks
    \* @type: Str -> Int;
    honestSlot \* a function mapping an honest validator to its local slot --- used for synchronization purpose

\* A helper function that maps slots to epochs
\* @type: Int => Int;
SlotInEpoch(slot) == ((slot - 1) \div SlotPerEpoch) + 1

\* the set of all possible valid blocktrees
AllValidTrees == { t \in [Blocks -> Blocks \union {NilBlock}] : t[GENESIS] = NilBlock 
    /\ \A b \in Blocks: t[b] < b }

\* Non-recursive version, enumerate some possibilities
ancestor(b1, b2) ==
    \/ b1 = blockTree[b2]
    \/ \E b3 \in Blocks: b3 = blockTree[b2] /\ b1 = blockTree[b3]
    \/ \E b3, b4 \in Blocks: b3 = blockTree[b2] /\ b4 = blockTree[b3] /\ b1 = blockTree[b4] \* sufficient for up to 3 slots

\* pick up the maximal element from a set of blocks, return -1 if empty set
\* @ *type: Set(Int) -> Int;
MaxBlock(blocks) == LET Max(p,q) == IF p > q THEN p ELSE q IN ApaFoldSet(Max, -1, blocks)

\* We let a FFG vote of each validator is of well formed, i.e., src < dst = slot
\* Even dishonest validators are supposed to obey this constraint
\* @type: (Set({id: Str, src: Int, dst: Int})) => Bool;
WellFormedFFG(votes) ==
    \A m \in votes: SlotInEpoch(m.src) < SlotInEpoch(m.dst) /\ ancestor(m.src, m.dst)

\* Each honest validator casts only 1 vote in each epoch
\* Each honest validator does not cast slashable/surrounding votes (stronger than the last version)
\* @type: (Set({id: Str, src: Int, dst: Int})) => Bool;
WellFormedHonestFFG(votes) ==
    \A m1, m2 \in votes: m1 = m2 \/ m1.id /= m2.id \/ (
        /\ SlotInEpoch(m1.dst) /= SlotInEpoch(m2.dst)
        /\ (SlotInEpoch(m1.src) >= SlotInEpoch(m2.src) \/ SlotInEpoch(m1.dst) < SlotInEpoch(m2.dst))
    )

\* Enforce the number of Byzantine votes
\* @type: (Set({id: Str, src: Int, dst: Int})) => Bool;
EnforceByzantineFFG(votes) ==
    Cardinality(votes) = BVotesLimit \* was <=

\* Enforce the number of honest votes as the number of honest validators (i.e., one vote per validator in each epoch)
\* @ *type: (Set({id: Str, src: Int, dst: Int})) => Bool;
\* EnforceHonestFFG(votes) ==
\*    /\ Cardinality(votes) = Honest
\*\*    /\ \A m \in votes: m.src = MaxBlock(justifiedBlocks[m.id])

\* the set of all possible FFG votes from dishonest and honest validators (may not be well formed)
AllDishonestFFG == [id: BValidators, src: Blocks, dst: Blocks]
\* AllHonestFFG == [id: HValidators, src: Blocks, dst: Blocks]

\* vars == <<blockTree, honestVotes, byzantineVotes, ffgVotes, receivedAttestations, justifiedBlocks, finalizedBlocks, honestSlot>>
vars == <<blockTree, byzantineVotes, receivedAttestations, justifiedBlocks, finalizedBlocks, honestSlot>>

(* Before protocol execution, we randomly generate a proposer function, a blockTree relation,
   a collection of FFG attestations from honest validators and a collection of FFG attestations
   from Byzantine validators.
*)        

Init == 
    /\ blockTree \in AllValidTrees
    /\ honestVotes = {}
    /\ byzantineVotes \in SUBSET AllDishonestFFG
    /\ WellFormedFFG(byzantineVotes)
    /\ EnforceByzantineFFG(byzantineVotes)
    /\ ffgVotes = byzantineVotes \* honestVotes \union byzantineVotes
    /\ receivedAttestations = [ v \in HValidators |-> {} ]
    /\ justifiedBlocks = [ v \in HValidators |-> {GENESIS} ]
    /\ finalizedBlocks = [ v \in HValidators |-> {GENESIS} ]
    /\ honestSlot = [ v \in HValidators |-> 1]
    /\ currentSlot = 0

(* 
  Each slot makes only one transition, which assigns a subset of attestations nondeterministically
  released so far to each honest validator.
  We check safety as invariant conditions that have to be satisfied in all reachable states.
*)


\* A set of FFG votes that are cast in slot [1..slot]
\* @type: (Set({id: Str, src: Int, dst: Int}), Int) => Set({id: Str, src: Int, dst: Int});
VotesInSlot(votes, slot) ==
    { m \in votes: m.dst <= slot }

\* Update validator v's collection of attestations 
UpdateView(v) ==
    receivedAttestations' = [receivedAttestations EXCEPT ![v] = receivedAttestations[v] \union VotesInSlot(ffgVotes, currentSlot)]

\* Define whether an block (Checkpoint) is regarded as justified by a validator from a justified src
\* @type: (Str, Int, Int) => Bool;
RealizedJustification(validator, b1, b2) ==
    /\ b2 \notin justifiedBlocks[validator]
    /\ b1 \in justifiedBlocks[validator] 
    /\ Cardinality({ a \in receivedAttestations'[validator]: a.src = b1 /\ a.dst = b2 }) >= THRESHOLD

\* Update validator v's view on justified blocks and finalized blocks
\* @type: (Str) => Bool;
UpdateJustified(validator) ==
    /\ justifiedBlocks' = [justifiedBlocks EXCEPT ![validator] = justifiedBlocks[validator] 
        \union { b2 \in Blocks: (\E b1 \in Blocks: RealizedJustification(validator, b1, b2)) }]
    /\ finalizedBlocks' = [finalizedBlocks EXCEPT ![validator] = finalizedBlocks[validator] 
        \union { b1 \in Blocks: (\E b2 \in Blocks: RealizedJustification(validator, b1, b2)) }]         
 
\* To update honest validator's votes in epoch e
\* @type: (Int) => Bool;
UpdateHonestAttestations(epoch) ==
    LET newVotes == { m \in [id: HValidators, src: Blocks, dst: { (epoch-1)*SlotPerEpoch+1 }] : m.src = MaxBlock(justifiedBlocks[m.id])} IN
    /\ ffgVotes' = ffgVotes \union newVotes
    /\ honestVotes' = honestVotes \union newVotes
    /\ WellFormedHonestFFG(honestVotes')

\* scala.NotImplementedError: A set filter over PowerSet[Set( {dst: Int, id: Str, src : Int})] is not implemented
\* A bug report has been generated at [.../Test_Gasper_no_recr_4_1.tla/2023-02-24T11-26-36_...]
\*    LET  newVotes == CHOOSE X \in SUBSET [id: HValidators, src: Blocks, dst: { s \in Slots: SlotInEpoch(s) = e }] : 
\*    WellFormedHonestFFG(X \union honestVotes) /\ EnforceHonestFFG(X) IN (ffgVotes' = ffgVotes \union newVotes /\ honestVotes' = honestVotes \union newVotes)

 \* System proceeds to the next slot
SlotProceed == 
    /\ \A v \in HValidators: honestSlot[v] > currentSlot
    /\ currentSlot < MaxSlot \* finite model
    /\ currentSlot' = currentSlot + 1 
    /\ IF (currentSlot+1)%SlotPerEpoch = 0 THEN UpdateHonestAttestations(SlotInEpoch(currentSlot+1)) ELSE ffgVotes' = ffgVotes /\ honestVotes' = honestVotes \* /\ newVotes' = newVotes
    /\ UNCHANGED vars

\* In the current slot, honest validator v collects attestations and update block views
ValidatorAction(v) == 
    /\ currentSlot <= MaxSlot \* was <
    /\ honestSlot[v] = currentSlot
    /\ honestSlot' = [honestSlot EXCEPT ![v] = honestSlot[v] + 1]
    /\ UpdateView(v) 
    /\ UpdateJustified(v)
    /\ UNCHANGED <<blockTree, currentSlot, byzantineVotes, honestVotes, ffgVotes>>

LiveLock ==
    /\ currentSlot = MaxSlot
    /\ currentSlot' = currentSlot
    /\ ffgVotes' = ffgVotes 
    /\ honestVotes' = honestVotes
    /\ UNCHANGED vars

Next == 
    \/ SlotProceed
    \/ \E v \in HValidators: ValidatorAction(v)
    \/ LiveLock

Safety ==
    \A v1, v2 \in HValidators:
        \/ v1 = v2
        \/ finalizedBlocks[v1] \subseteq finalizedBlocks[v2]
        \/ finalizedBlocks[v2] \subseteq finalizedBlocks[v1]

\* This property should be falsified
Liveness ==
    currentSlot /= MaxSlot \/ (\E v \in HValidators: honestSlot[v] <= MaxSlot) \/ (\E b\in Blocks: b/= GENESIS /\ (\A v \in HValidators: b \in finalizedBlocks[v]))

\* A weaker condition than Liveness
JustificationLiveness ==
    currentSlot /= MaxSlot \/ (\E v \in HValidators: honestSlot[v] <= MaxSlot) \/ (\E b\in Blocks: b/= GENESIS /\ (\A v \in HValidators: b \in justifiedBlocks[v]))

=============================================================================

\*Init == honestVotes = {[id |-> "aa", slot |-> 1, src |-> 1, dst |-> 2]}

