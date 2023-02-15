# Gasper-TLA-
TLA+ models for the Gasper consensus protocol

### The first model in "Gasper_all_msg_000.tla" produces too many states and causes out-of-memory 
(max JVM memory: 4294967296 ~ 4G)

### The second model, in "Gasper_all_msg_000_simplified.tla", performs the following simplifications.

- Removing the block tree (a mapping from each block to its parent), and let the block tree structure be implicitly encoded in the set of (honest and byzantine) Attestations

- Enforcing a limit on the number of byzantine Attestations as 2 votes per epoch

- I have aborted the checking for the second model after 1 day 2 hours 49 minutes in a MacBookPro M1 Pro (MacOS 13.01, Memory 16GB).

### The third model in "Gasper_all_msg_000_string.tla"

- Representing validators by strings

- Using honestSlot to synchronize local time of all validators

- Safety property is verified with 581 seconds in a MacBookPro M1 Pro (MacOS 13.01, Memory 16GB).

### Usage

- Install the most recent versioned apalache (currently v0.30.1) from https://github.com/informalsystems/apalache/releases

- Install Java 11 jdk (I used https://www.oracle.com/au/java/technologies/javase/jdk11-archive-downloads.html)

- Under the folder "protocol", type:

  apalache-mc check --inv=FinalitySafety Test_Gasper_string_4_1.tla
  
  (for 3 honest validators + 1 byzantine validator, 3 epochs each has 1 slot)
