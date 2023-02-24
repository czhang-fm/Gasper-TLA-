----------------------------- MODULE Test_Gasper_no_recur_4_1 -------------------------------

\* the variables declared in the Gasper protocol
VARIABLES
    \* @type: Int -> Int;
    blockTree,
    \* @type: Set({id: Str, src: Int, dst: Int});
    honestVotes,
    \* @type: Set({id: Str, src: Int, dst: Int});
    byzantineVotes,
    \* @type: Set({id: Str, src: Int, dst: Int});
    ffgVotes,      \* a set of FFG votes of record type [id: Validator, slot, src: Epoch, dst: Block]
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

INSTANCE Gasper_all_msg_001_no_recur WITH 
    Honest <- 3,
    Byzantine <- 1,
    HValidators <- {"v1", "v2", "v3"},
    BValidators <- {"b1"},
    NumEpoch <- 4,
    SlotPerEpoch <- 1


=============================================================================  