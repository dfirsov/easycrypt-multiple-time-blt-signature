## Verified Multiple-Time Signature Scheme from One-Time Signatures and Timestamping

This repository contains the EasyCrypt code associated with the paper "D. Firsov, H. Lakk, A. Truu. [Verified Multiple-Time Signature Scheme from One-Time Signatures and Timestamping](https://eprint.iacr.org/2021/528)".

## Contents
 - [Timestamp.ec](Timestamp.ec) - ideal model of backdating resistant timestamping.
 - [OTS.ec](OTS.ec) - Abstract definitions related to one-time signature schemes.
	 - [OTS/Lamport.ec](OTS/Lamport.ec) - Introduction to Easycrypt: Implementation and the security proof of the one-bit Lamport signature.
	 - [OTS/OTSM.ec](OTS/OTSM.ec) - Auxiliary scheme where M one-time keypairs are generated and adversary wins if they manage to forge a signature for at least one of the keypair.
	 - [OTS/OTSM2OTS.ec](OTS/OTSM2OTS.ec) - The lemma "otsm2otsUB" relates the probability of success in OTSM game to the success in OTS  game.
 - [Tags.ec](Tags.ec) - Abstract definitions related to multiple-time tag-systems.  
	 - [Tags/MultipleTimeConstruction.ec](Tags/MultipleTimeConstruction.ec) - The implementation of stateless multiple-time tag system from one-time signatures (motivated by "authentication trees" of Merkle and Goldreich). The lemma "multTagsCorrect" proves that for valid keypairs the tag verification agrees with tag generation.
	 - [Tags/ForwardResistance_Independent_Keys.ec](Tags/ForwardResistance_Independent_Keys.ec) - The lemma "fr2otsUB" proves that the forward-resistance of the implemented multiple-time tag system with independently generated keypairs is upper bounded by existential unforgeability of the underlying one-time signatures scaled by M.
	 - [Tags/ForwardResistance_PRF_Keys.ec](Tags/ForwardResistance_PRF_Keys.ec) - The lemma "fr2otsAndPRFUB" proves that the forward-resistance of the implemented multiple-time tag system with PRF induced keypairs is upper bounded by existential unforgeability of the underlying one-time signatures scaled by M plus the indistinguishability of the PRF.
 - [BLT.ec](BLT.ec) - The implementation of multiple-time BLT signature scheme parameterized by timestamping repository and multiple-time tag system.
	 - [BLT/BLT2FR.ec](BLT/BLT2FR.ec) - The lemma "blt2frUB" shows that the existential unforgeability of the multiple-time BLT scheme is upper bounded by multiple-time forward-resistance of the underlying tag system.
 - [KeyGen.ec](KeyGen.ec) - module type of secret key generators
	 - [KeyGen/TagKeysEff.ec](KeyGen/TagKeysEff.ec) - The lazy (efficient) PRF based key generation is equivalent to the eager PRF based key generation.
	 - [KeyGen/OTSMKeys.ec](KeyGen/OTSMKeys.ec) - resampling keys in the table randomly sampled table does not change the distribution of the key table.
 * [Hash.ec](Hash.ec)  - hash function and the pre-image resistance game
 * [BasicProps.ec](BasicProps.ec) - basic frequently used properties and functions
 *  [PRF/](PRF) - the EasyCrypt stdlib definitions of PRF. 

## Setup
- For this project we used the version of EasyCrypt (1.0) theorem prover with GIT hash: r2022.04-48-gc8d3d6c1.
- EasyCrypt was configured with support from the following SMT solvers: Why3@1.5.0, Z3@4.8.7, CVC4@1.6, Alt-Ergo@2.4.1.
- To check the development run:
      $> cd DEVELOPMENT_FOLDER
      $> bash checkall
- If you want to typecheck this code in Emacs then you must update your load path. Make sure your `~/.emacs` file contains the following load paths:

      '(easycrypt-load-path
       (quote
        ( "DEVELOPMENT_PATH/KeyGen" 
          "DEVELOPMENT_PATH/OTS"
          "DEVELOPMENT_PATH/BLT"
          "DEVELOPMENT_PATH/PRF"
          "DEVELOPMENT_PATH/Tags")))
