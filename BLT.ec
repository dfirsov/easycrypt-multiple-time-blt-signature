require import FSet Int Real SmtMap Distr List.

(* the BLT_Scheme_Theory derives Multiple-Time BLT signature from
Multiple-Time Tag System and Timestamping *)
theory BLT_Scheme_Theory.

(* type and function parameters *)
type Time = int.
type pkey, skey, tag, message.
op tagGen : skey -> Time -> tag option.
op tagVer : pkey -> Time -> tag option -> bool.
op tdistr : int distr.
op EXP : Time.
op dR : int distr.

require Timestamp.
clone export Timestamp.Timestamping  with type data   <- message * tag option,
                                          op   tdistr <- tdistr.

require Tags.
clone export Tags.TagSystem  with type pkey       <- pkey,
                                  type skey       <- skey,
                                  type tag        <- tag,
                                  op tagGen       <- tagGen,
                                  op tagVer       <- tagVer,
                                  op EXP          <- EXP,
                                  op dR           <- dR.


(* module type of a BLT oracles *)                                  
module type BLTOracleT = {
  proc init(pk:pkey, sk:skey) : unit
  proc sign(m : message) : Time * tag option
  proc fresh(m : message) : bool
}.


(* BLT adversary has an access to the timestamping repository and BLT oracle  *)
module type AdvBLT (T : Repo, B : BLTOracleT) = {
  proc forge(pk:pkey) : Time * tag option * message {B.sign, T.put}
}.


(* the standard implementation of BLT oracle parameterized by
Timestamping service and tagging oracle *)
module BLTOracle (R : Repo, T : TagOracleT) : BLTOracleT = {
  var l : message list
  proc init(pk : pkey, sk : skey) = {
    R.init();
    T.init(pk, sk);
    l <- [];
  }  
  proc sign(m : message) = { 
     var t, tg;
     t <@ R.clock();
     tg <@ T.tag(t+1); 
     R.put(m, tg);
     l <- m :: l;
     return (t, tg);
  }
  proc fresh(m : message) : bool = {
     return !(m \in l);
  }  
}.


(* The BLT game formalizes the idea of existential unforgeability
under chosen messages for the family of multiple-time BLT
signatures *)
module GameBLT(A : AdvBLT, R : Repo, BLT : BLTOracleT, K : KeyGenT) = {
  module A = A(R, BLT)
  var r : bool
  var i : int
  var tg : tag option
  var m : message
  proc main() : bool = {
    var pk, sk, fresh, timestamped;
    (pk, sk) <@ K.keyGen();    
    BLT.init(pk, sk);
    (i, tg, m) <@ A.forge(pk);
    timestamped <@ R.check(i, (m, tg));
    fresh <@ BLT.fresh(m);
    r <- i <= EXP /\ tagVer pk i tg /\ fresh /\ timestamped;
    return  r;
  }
}.

end BLT_Scheme_Theory.
