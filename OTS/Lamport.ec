require import AllCore List Distr DBool.

(* The goal of the development in this file is to introduce basic
concepts behind EasyCrypt by implementing and proving the security of
the one-bit Lamport signature. 


The lemma lamportSecurity establishes that the probability of forging
the signature (for the bit false) for the Lamport scheme is upper bounded by the
probability of successful breaking the pre-image resistiance of the
hash function.

Since the case of forging the signature for the bit true is completely
symmetrical then the second half of the proof is left as an exercise
to the curious reader.
*)

require Hash.
clone export Hash.Hash_Theory.

(* instantiating the types and functions   *)
type skey = r * r.
type pkey = r * r.
type sig  = r * r.
type msg  = bool.

op otsSig  (sk : skey) (b : msg) : sig = b ? (sk.`1 , h sk.`2) : (h sk.`1, sk.`2).

op otsVer (pk : pkey option) (b : msg) (s : sig) : bool 
 = b ? (h s.`1 = (oget pk).`1 /\    s.`2 = (oget pk).`2) 
     : (s.`1   = (oget pk).`1 /\  h s.`2 = (oget pk).`2).



(* importing the key generation and the OTS framework *) 
require KeyGen.
clone export KeyGen.KeyGen as KG with type skey <- skey,
                                      type pkey <- pkey.
                                
require OTS.
clone export OTS.OTS_Theory as OT with type skey <- skey,
                                       type pkey <- pkey,
                                       type message  <- msg,
                                       type sig  <- sig,
                                       op otsSig <- otsSig,
                                       op otsVer <- otsVer.

(* Lamport key generation module *)
module LKG : KeyGenT  = {
  proc keyGen() : pkey * skey = {
    var sk1, sk2 : r;
    sk1 <$ rDistr;
    sk2 <$ rDistr;
    return ((h sk1, h sk2), (sk1, sk2));
  }
}.

(* One-Time signing oracle *)
module LO : OTSOracleT = {
 var sk : skey
 var m : msg option 
 proc init(pk : pkey, sk : skey) = {
  LO.sk <- sk;
  LO.m <- None;
 }
 proc sign(b : msg) : sig option = {
   var result <- witness;
   if(m = None){
      result <- if b then (sk.`1 , h sk.`2) else (h sk.`1, sk.`2);
      m <- Some b;
   }
   return Some result;
 }
 proc verify(b : msg, s : sig) : bool = {
   return if b then (h s.`1 = h sk.`1 /\  s.`2 = h sk.`2) 
            else (s.`1 = h sk.`1 /\  h s.`2 = h sk.`2);
 }
 proc fresh(b : msg) : bool = {
   return Some b <> m;
 }
}.


(* Correctness of Lamport Signature: verification 
   agrees with signature generation *)
module LamportCorrect = {
  proc correct(b : bool) = {
    var sk : skey;
    var pk : pkey;
    var correct : bool;
    var signature : sig option;
    (pk, sk) <@ LKG.keyGen();
    LO.init(pk, sk);
    signature <@ LO.sign(b);
    correct <@ LO.verify(b, oget signature);
    return correct;
  }
}.


lemma lamportCorrect : hoare[ LamportCorrect.correct : true ==> res ].
proof. proc. inline*. wp. rnd. rnd. skip. progress.
qed.



(* Security *)

(*
If A is successful in breaking the Lamport signature for message
"GameOTS.m = false" then we know that "m" is fresh which means that A
did not ask signing oracle to sign it and at most he used signing
oracle to sign "true".
*)
module LO' : OTSOracleT = {
 var v  : r
 var pk : r
 var m  : msg option
 proc init(pk : pkey, sk : skey) = {
  LO'.v <- sk.`1;
  LO'.pk <- h sk.`2;
  LO'.m <- None;
 }
 proc sign(b : msg) : sig option = {
   var result <- witness;
   if(m = None){
      result <- (v, pk);
      m <- Some b;
   }
   return Some result;
 }
 proc fresh(b : bool) : bool = {
   return Some b <> m;
 }
 proc verify(b : bool, s : sig) : bool = {
   var result : bool;
   result <- (s.`1 = h v /\ h s.`2 = pk);
   return result; 
 }
}.

(*
Recap: A succesfully forges Lamport signature for m=false. Preimage
resistance adverasry OTS2PRE(A) receives a value "v : r" and must find
its preimage.

Since the signature for the message false is (h r1, r2) then we
generate r1 and set the Lamport public key to be (h r1, v).

For A to function properly we need supply him the signing oracle, but
can we?
*)
module OTS2PRE(A : AdvOTS) : AdvPRE  = {
  module A = A(LO')
  var b : bool
  proc forge(v : r) = {
    var r,  m, s;
    r <$ rDistr;
    LO'.m <- None;
    LO'.v <- r;
    LO'.pk <- v;
    (m, s) <@ A.forge((h r, v));
    return s.`2;
  }
}.


section.
declare module A <: AdvOTS{-GamePRE, -GameOTS, -LO, -LO'}.
axiom loEquiv_is : forall (B <: OTSOracleT{-A}), islossless B.sign => islossless A(B).forge.

(* If A forges a signature for "false" then oracle LO and LO' are indistinguishable *)
lemma loEquiv : equiv [ GameOTS(LO', A, LKG).main 
          ~ GameOTS(LO, A, LKG).main
         : ={glob A, glob GameOTS} 
         ==> (GameOTS.m{2} = false /\ res{2}) 
               => (GameOTS.m{1} = false /\ res{1}) ].
proof. proc. inline*. wp.
call (_: LO.m = Some false, 
     (LO'.pk{1} = h LO.sk{2}.`2 
   /\ LO'.v{1} = LO.sk{2}.`1 
   /\ LO'.m{1} = LO.m{2}), 
      LO'.pk{1} = h LO.sk{2}.`2 
   /\ LO'.v{1} = LO.sk{2}.`1 
   /\ LO.m{2} = Some false).
apply loEquiv_is.
proc. wp. skip. progress.
have : b{2} = true. smt.
move => h. rewrite h. simplify. auto.
move => &1 z.
proc. wp. skip. progress.
move => &1. 
proc. wp. skip. progress. 
wp. rnd. rnd. skip. progress;smt.
qed.


(* if A wins OTS game with LO' then OTS2PRE(A) wins PRE game *)
lemma ots2preEq : equiv [ 
   GameOTS(LO', A, LKG).main 
  ~ GamePRE(OTS2PRE(A)).main : 
  ={glob A} ==> res{1} /\ GameOTS.m{1} = false  => res{2} ].
proof. proc.
inline LKG.keyGen.
swap {1} 1 1.
inline*. wp.
call (_: ={LO'.v, LO'.pk, LO'.m} ). 
proc. wp. skip. progress. wp.
rnd. wp. rnd. skip. progress.  smt.
qed.



lemma loProb &m : 
    Pr[ GameOTS(LO, A, LKG).main() @ &m : res /\ GameOTS.m = false ] 
 <= Pr[ GameOTS(LO', A, LKG).main() @ &m : res  /\ GameOTS.m = false].
proof. byequiv (_ : ={glob A, glob GameOTS}  ==> _). 
symmetry. conseq loEquiv. progress;smt. smt. auto. auto.
qed.


lemma loOTS2Pre &m : 
     Pr[ GameOTS(LO', A, LKG).main() @ &m : res /\ GameOTS.m = false ] 
 <=  Pr[ GamePRE(OTS2PRE(A)).main() @ &m : res ].
proof. byequiv (_ : ={glob A}  ==> _). conseq ots2preEq. progress. smt. 
qed.


(* The probability of A forging signature for false is upper-bounded
by probability of OTS2PRE(A) breaking the preimage resistance.  Same
holds for the "true" case.
*)
lemma lamportSecurity &m : 
    Pr[ GameOTS(LO, A, LKG).main() @ &m : res /\ GameOTS.m = false ]
 <= Pr[ GamePRE(OTS2PRE(A)).main() @ &m : res ].
proof. smt.
qed.
