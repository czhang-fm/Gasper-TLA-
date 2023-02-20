# Gasper-TLA-
TLA+ models for the Gasper consensus protocol

### The first model in "Gasper_all_msg_000.tla" produces too many states and causes out-of-memory 
(max JVM memory: 4294967296 ~ 4G)

### The second model, in "Gasper_all_msg_000_simplified.tla", performs the following simplifications.

- Removing the block tree (a mapping from each block to its parent), and let the block tree structure be implicitly encoded in the set of (honest and byzantine) Attestations

- Enforcing a limit on the number of byzantine Attestations as 2 votes per epoch

- I have terminated the verification procedure for the second model after 1 day 2 hours 49 minutes on a MacBookPro M1 Pro (MacOS 13.01, Memory 16GB).

### The third model in "Gasper_all_msg_000_string.tla"

- Representing validators by strings

- Using honestSlot to synchronize local time of all validators

- On a MacBookPro M1 Pro (MacOS 13.01, Memory 16GB):

Safety property is verified with 9 minutes 41 seconds (3 honest validators + 1 byzantine validator, 3 epochs each with 1 slot),
and ran out of memory after 5 minutes 16 seconds (3 honest validators + 1 byzantine validator, 4 epochs each with 2 slots).

### The fourth model in "Gasper_all_msg_000_restricted.tla"

- Added more restrictions on honest validators behavior, so that each has to vote exactly once in each epoch
- Added a simple liveness condition (which can be shown as false)

### The fifth model in "Gasper_all_msg_001_scheduled.tla"

- The honest validators are supposed to release votes gradually, at the end of each epoch
- This adds more complexity to the model at it ran out of memory for 3 epochs with 3+1 validators (MacOS 13.01, Memory 16GB)

### The sixth model in "Gasper_all_msg_no_honest.tla"

- This model removes all honest attestations, and only tests the complexity of the model when only byzaninte attestations are present

### Usage

- Install the most recent versioned apalache (currently v0.30.1) from https://github.com/informalsystems/apalache/releases
- Alternatively, a docker option is available for apalache, following from https://apalache.informal.systems/docs/apalache/installation/docker.html
(however I haven't personally tested this option in any system)

- Install Java 11 jdk (I used https://www.oracle.com/au/java/technologies/javase/jdk11-archive-downloads.html)

- Under the folder "protocol", type:

  apalache-mc check --inv=FinalitySafety Test_Gasper_string_4_1.tla  (showing safety, 3 epochs each with 1 slot)
  
  apalache-mc check --inv=Liveness Test_Gasper_restricted_4_1.tla  (producing a counterexample for livness, 2 epochs each with 1 slot)
  
For the sixth model with all honest attestation removed, currently it's set up with 5 epochs each with 1 slot, for 3 honest validators + 1 byzantine validator.

- Under the folder "protocol", type:

  apalache-mc check --inv=FinalitySafety Test_Gasper_no_honest_4_1.tla 
