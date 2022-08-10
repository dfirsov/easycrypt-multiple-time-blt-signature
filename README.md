## Contents

 * Timestamping.ec - ideal model of backdating resistant timestamping.

 * OTS.ec - Abstract definitions related to one-time signature
   schemes.

 ** OTS/Lamport.ec - Introduction to Easycrypt: Implementation and the
    security proof of the one-bit Lamport signature.

 ** OTS/OTSM.ec - Auxiliary scheme where M one-time keypairs are
    generated and adversary wins if they manage to forge a signature
    for at least one of the keypair.

 ** OTS/OTSM2OTS.ec - The lemma "otsm2otsUB" relates the probability of
    success in OTSM game to the success in OTS game.

 * Tags.ec - Abstract definitions related to multiple-time
   tag-systems.
   
 ** Tags/MultipleTimeConstruction.ec - The implementation of stateless
    multiple-time tag system from one-time signatures (motivated by
    "authentication trees" of Merkle and Goldreich). The lemma
    "multTagsCorrect" proves that for valid keypairs the tag
    verification agrees with tag generation.

 ** Tags/ForwardResistance_Independent_Keys.ec - The lemma "fr2otsUB"
    proves that the forward-resistance of the implemented
    multiple-time tag system with independently generated keypairs is
    upper bounded by existential unforgeability of the underlying
    one-time signatures scaled by M.
    
 ** Tags/ForwardResistance_PRF_Keys.ec - The lemma "fr2otsAndPRFUB"
    proves that the forward-resistance of the implemented
    multiple-time tag system with PRF induced keypairs is upper
    bounded by existential unforgeability of the underlying one-time
    signatures scaled by M plus the indistinguishability of the PRF.

 * BLT.ec - The implementation of multiple-time BLT signature scheme
   parameterized by timestamping repository and multiple-time tag
   syste.

 ** BLT/BLT2FR.ec - The lemma "blt2frUB" shows that the existential
   unforgeability of the multiple-time BLT scheme is upper bounded by
   multiple-time forward-resistance of the underlying tag system.

 * KeyGen.ec - module type of secret key generators

 ** KeyGen/TagKeysEff.ec - The lazy (efficient) PRF based key
    generation is equivalent to the eager PRF based key generation.

 ** KeyGen/OTSMKeys.ec - resampling keys in the table randomly sampled
    table does not change the distribution of the key table.

 * Hash.ec       - hash function and the pre-image resistance game
 * BasicProps.ec - basic frequently used properties and functions
 
 * PRF.ec and PRF/* - the EasyCrypt stdlib definitions of PRF. 



## Setup


* For this project we used the developement version of EasyCrypt (1.0)
theorem prover with git-hash: a9666b1169211145c65a107756d6c706b007b7d8.

* EasyCrypt was configured with support from the following SMT solvers:
Why3@1.2.0, Z3@4.7.1, CVC4@1.6, CVC4@1.6, Alt-Ergo@2.3.0

* load-path must contain the path to the folder and subfolders of this
  development.

* to check the development run:
  
  $> cd DEVELOPMENT_FOLDER
  $> bash checkall
