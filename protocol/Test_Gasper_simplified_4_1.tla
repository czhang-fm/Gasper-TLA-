----------------------------- MODULE Test_Gasper_simplified_4_1 -------------------------------

\* the variables declared in the Gasper protocol
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

INSTANCE Gasper_all_msg_000_simplified WITH 
    Honest <- 3,
    Byzantine <- 1,
    NumEpoch <- 3,
    SlotPerEpoch <- 1


=============================================================================  