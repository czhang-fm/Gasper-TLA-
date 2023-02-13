-------------------- MODULE Gasper_all_msg_000_simplified ---------------------------
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
       
EXTENDS Integers, FiniteSets

CONSTANTS 
    \* @type: Int;
    Honest,        \* number of honest validators
    \* @type: Int;
    Byzantine,     \* number of byzantine validators
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
HValidators == 1..Honest
BValidators == (Honest+1)..(Honest+Byzantine)
Validators == HValidators \union BValidators
NumValidators == Honest + Byzantine
ValidatorPerSlot == NumValidators \div SlotPerEpoch \* integer division, to check later
Epochs == 0..NumEpoch  \* epoch 0 is reserved for GENESIS block
THRESHOLD == Byzantine * 2 + 1
BVotesLimit == Byzantine * NumEpoch * 2

(***************** STATE VARIABLES **********************************)
VARIABLES
    \* @type: Set({id: Int, slot: Int, src: Int, dst: Int});
    honestVotes,
    \* @type: Set({id: Int, slot: Int, src: Int, dst: Int});
    byzantineVotes,
    \* @type: Set({id: Int, slot: Int, src: Int, dst: Int});
    ffgVotes,      \* a set of FFG votes of record type [id: Validator, slot, src: Epoch, dst: Block]
    \* @type: Int;
    currentSlot,
    \* @type: Int -> Set({id: Int, slot: Int, src: Int, dst: Int});
    receivedAttestations, \* a function mapping an honest validator to attestations(slots) that he has received so far
    \* @type: Int -> Set(Int);
    justifiedBlocks, \* a function mapping an honest validator to a set of justified blocks
    \* @type: Int -> Set(Int);
    finalizedBlocks \* a function mapping an honest validator to a set of finalized blocks

\* A helper function that maps slots to epochs
\* @type: Int => Int;
SlotInEpoch(slot) == ((slot - 1) \div SlotPerEpoch) + 1

\* We let a FFG vote of each validator is of well formed, i.e., src < dst = slot
\* Even dishonest validators are supposed to obey this constraint
\* @type: (Set({id: Int, slot: Int, src: Int, dst: Int})) => Bool;
WellFormedFFG(votes) ==
    \A m \in votes: (SlotInEpoch(m.src) < SlotInEpoch(m.dst) 
       /\ SlotInEpoch(m.dst) = SlotInEpoch(m.slot) )

\* Each honest validator casts only 1 vote in each epoch
\* Each honest validator does not cast slashable/surrounding votes (stronger than the last version)
\* @type: (Set({id: Int, slot: Int, src: Int, dst: Int})) => Bool;
WellFormedHonestFFG(votes) ==
    \A m1, m2 \in votes: m1.id /= m2.id \/ (
        /\ SlotInEpoch(m1.slot) /= SlotInEpoch(m2.slot)
        /\ (SlotInEpoch(m1.src) >= SlotInEpoch(m2.src) \/ SlotInEpoch(m1.slot) < SlotInEpoch(m2.slot))
    )

\* Enforce the number of Byzantine votes
\* @type: (Set({id: Int, slot: Int, src: Int, dst: Int})) => Bool;
EnforceByzantineFFG(votes) ==
    Cardinality(votes) <= BVotesLimit

\* the set of all possible FFG votes from dishonest and honest validators (may not be well formed)
AllDishonestFFG == [id: BValidators, slot: Slots, src: Blocks, dst: Blocks]
AllHonestFFG == [id: HValidators, slot: Slots, src: Blocks, dst: Blocks]

vars == <<honestVotes, byzantineVotes, ffgVotes, receivedAttestations, justifiedBlocks, finalizedBlocks>>

(* Before protocol execution, we randomly generate a proposer function, a blockTree relation,
   a collection of FFG attestations from honest validators and a collection of FFG attestations
   from Byzantine validators.
*)        

Init == 
    /\ honestVotes \in SUBSET AllHonestFFG
    /\ byzantineVotes \in SUBSET AllDishonestFFG
    /\ WellFormedFFG(byzantineVotes)
    /\ WellFormedFFG(honestVotes)
    /\ WellFormedHonestFFG(honestVotes)
    /\ EnforceByzantineFFG(byzantineVotes)
    /\ ffgVotes = honestVotes \union byzantineVotes
    /\ receivedAttestations = [ v \in HValidators |-> {} ]
    /\ justifiedBlocks = [ v \in HValidators |-> {GENESIS} ]
    /\ finalizedBlocks = [ v \in HValidators |-> {GENESIS} ]
    /\ currentSlot = 1

(* 
  Each slot makes only one transition, which assigns a subset of attestations nondeterministically
  released so far to each honest validator.
  We check safety as invariant conditions that have to be satisfied in all reachable states.
*)

\* A set of FFG votes that are cast in slot [1..slot]
\* @type: (Set({id: Int, slot: Int, src: Int, dst: Int}), Int) => (Set({id: Int, slot: Int, src: Int, dst: Int}));
VotesInSlot(votes, slot) ==
    { m \in votes: m.slot <= slot }

\* Update validator v's collection of attestations 
UpdateView(v) ==
\*    \E ffg \in SUBSET VotesInSlot(ffgVotes, currentSlot):
    receivedAttestations' = [receivedAttestations EXCEPT ![v] = receivedAttestations[v] \union VotesInSlot(ffgVotes, currentSlot)]

\* Define whether an block (Checkpoint) is regarded as justified by a validator from a justified src
RealizedJustification(validator, b1, b2) ==
    /\ b2 \notin justifiedBlocks[validator]
    /\ b1 \in justifiedBlocks[validator] 
    /\ Cardinality({ a \in receivedAttestations'[validator]: a.src = b1 /\ a.dst = b2 }) >= THRESHOLD

\* Update validator v's view on justified blocks and finalized blocks
UpdateJustified(validator) ==
    /\ justifiedBlocks' = [justifiedBlocks EXCEPT ![validator] = justifiedBlocks[validator] 
        \union { b2 \in Blocks: (\E b1 \in Blocks: RealizedJustification(validator, b1, b2)) }]
    /\ finalizedBlocks' = [finalizedBlocks EXCEPT ![validator] = finalizedBlocks[validator] 
        \union { b1 \in Blocks: (\E b2 \in Blocks: RealizedJustification(validator, b1, b2)) }]         
 
 \* System proceeds to the next slot
SlotProceed == 
    /\ currentSlot' = (IF currentSlot /= MaxSlot THEN currentSlot + 1 ELSE currentSlot) \* finite model
    /\ UNCHANGED vars

\* In the current slot, honest validator v collects attestations and update block views
ValidatorAction(v) == 
    /\ UpdateView(v) 
    /\ UpdateJustified(v)
    /\ UNCHANGED <<currentSlot, honestVotes, byzantineVotes, ffgVotes>>

Next == 
    \/ SlotProceed
    \/ \E v \in HValidators: ValidatorAction(v)

FinalitySafety ==
    \A v1, v2 \in HValidators:
        \/ finalizedBlocks[v1] \subseteq finalizedBlocks[v2]
        \/ finalizedBlocks[v2] \subseteq finalizedBlocks[v1]

=============================================================================


