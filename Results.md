# Summarizing the experiment results

The aim of the experiment is to build finite state models and to apply apalache to model check properties on instances of the Gasper protocol (https://arxiv.org/abs/2003.03052) or a simplified version of Gasper.

## Modelling techniques

We first summarize the component of a typical Gasper protocol. Such a protocol consists of 
1. a set of honest validators (HValidators) and a set of byzantine validator (BValidators) and it is required that size(HValidators) >= 2 * size(BValidators) + 1;
2. Epochs and slots are synchronous features of the Gasper protocol. Only one valid block can be proposed for each epoch, and at most one block (paired with an epoch value) can be justified per epoch. Moreover, an honest validator can cast an FFG vote (an attestation) at most once per epoch. To enforce a finite model, the number of epochs in the model (NumEpoch) and the number of slots per epoch (SlotPerEpoch) are set up as global constants provided by test files;
3. A block structure (blockTree) is modelled as a function from Slots to Slots. This is because we do not distinguish blocks from the slots where they are allocated (one block to be proposed in each slot), and use the slot index for each block. blockTree(b) returns the parent block of b. If b is not proposed, or the block is GENESIS (which has index 0), then blockTree(b) = -1;
4. The set of all attestations from Byzantine validators are decided at the beginning of a run (byzantineVotes \in SUBSET AllDishonestFFG). The same rule applies on honest validators, too (honestVotes \in SUBSET AllHonestFFG).
5. The constraints applied on the initial set of FFGs: (1) src < dst <= slot, where src is the source Checkpoint, dst is the target Checkpoint, and slot represent the time period in which the attestation is cast. (2) the set of Honest attestations (honestVotes) further needs to satisfy the nonslashability conditions, specified in WellFormedHonestFFG(votes); 
6. During the progress of the model, we release a subset of ffgVotes to each honest validators via UpdateView(v). Then UpdateJustified(v) will update the set of justifiedBlocks and finalizedBlocks for each validator v.

## Experiments

We summarize the design and performance of each model in this repository. I am testing the models in MacBookPro Apple M1Pro (Ventura 13.0.1) 16GB. The default setting is of max JVM memory 4G.

1. The first model "Gasper_all_msg_000.tla" implements all above features, and runs out of memory immediately. I didn't make any follow up trial.

2. The second model "Gasper_all_msg_000_simplied.tla", is tested with "Test_Gasper_simplified_4_1.tla" with 3 epoch (1 slot per epoch) and 3 Honest + 1 Byzantine validators. The blockTree structure has been removed from this model, and one additional constraint is put in place (EnforceByzantineFFG(votes)) which is used to limit the maximal number of Byzantine votes by 2 votes per epoch per validator (as a total count). The number of epoch is also set as 3, with 1 slot per epoch, and the safety verification cannot terminate with the default 4G JVM memory. I terminated the process after 1 day 2 hours 49 minutes.

3. The third model "Gasper_all_msg_000_string.tla", is tested with "Test_Gasper_string_4_1.tla". Two changes have been introduced in this model from "Gasper_all_msg_000_simplified.tla". The first change is that we represent each validator by a string. This may help with the constraint solver if the initial set of string is finite, while using integers to encode validators may complicate the formula to be solved, which may just be a speculation (as I don't understanding how apalache works from the inside). The second change is that a function honestSlot is introduced which maps HValidators to 1..MaxSlot, and we use this function to synchronize each honest validator's local time with the global time which is encoded in the variable "currentSlot".

This is the first time that we can actually terminate the verification procedure. For (3 honest + 1 byzantine) 3 epochs with 1 slot per epoch, the model is able to verify safety with the default setting after 9 minutes 41 seconds. The verification does not terminate when we increase the complexity to 4 epochs with 2 slots per epoch. (Shall we explore more on this model and the next model??)

4. The fourth model "Gasper_all_msg_000_restricted.tla" is tested with "Test_Gasper_restricted_4_1.tla". In this model we impose more restrictions on the honest validators so that in each honest validator is only allowed to vote once per epoch (this doesn't affect result if an epoch has only 1 slot). We also introduce a liveness condition, which can be checked as false with a counterexample being produced (for 2 epochs only). The liveness condition is expressed as at the end of the run (i.e., at MaxSlot) there exists a block v in all honest validators' finalizedBlocks such that v is not GENESIS. This invariance should be falsified for longer runs with more epochs.

5. In the fifth model "Gasper_all_msg_001_scheduled.tla", we set up a way to release 1 vote per epoch at the last slot of that epoch. It seems this change has complicated the model's structure and it ran out of memory for 3 epochs with 3+1 validators, with the default JVM setting.

6. The sixth model "Gasper_all_msg_no_honest.tla" is an effort to locate where the complexities arise from the our way of modelling. It is branched out from "Gasper_all_msg_000_string.tla" (the third model), and it removes all honest attestations (i.e., removing the variable 'honestVotes' and related structures). The model is tested with "Test_Gasper_no_honest_4_1.tla" for 3 honest validators and 1 byzantine validator, on the default JVM setting (4G memory), and it is later extended to 8G memory for follow-up tests. The results are presented in the following table.

| 3 epochs | 4 epochs  | 5 epochs | 6 epochs |
| ------| ------ | ------ | ----- |
| 6 sec (4G)  | 5 min 39 sec (4G) | out-of-mem (4G) | N/A |
| N/A   |  (8G) | 21 min 2 sec (8G) | out-of-mem (8G) |



 

