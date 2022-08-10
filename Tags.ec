require import Int Bool Distr AllCore List.

abstract theory TagSystem.

(* types *)
type pkey, skey, tag.
type Time = int.


(* pure tag generation and tag verification functions *)
op tagGen : skey -> Time -> tag option.
op tagVer : pkey -> Time -> tag option -> bool.


(* expiration date *)
op EXP : Time.
op dR : int distr.


(* key generation modules and types *)
require import KeyGen.
clone export KeyGen with type pkey <- pkey,
                         type skey <- skey,
                         op   dR <- dR.


(* module type of a tagging oracle *)                         
module type TagOracleT = {
  proc init(pk:pkey, sk:skey) : unit
  proc tag(t : Time)            : tag option
  proc getTagLog()              : Time list
}.


(* AdvFR represents the set of "reasonably efficient" adversaries *)
module type AdvFR (T : TagOracleT) = {
  proc forge(pk:pkey) : Time * tag option {T.tag}
}.


(* standard implementation of a multiple-time tagging oracle *)
module TagOracle  : TagOracleT = {
  var lt : Time list
  var pk : pkey  
  var sk : skey
  proc init(pk:pkey, sk:skey) = {
    TagOracle.pk <- pk;
    TagOracle.sk <- sk;
    lt <- [];
  }
  proc tag(t : Time) = {
    var tg;
    lt <- t :: lt;
    tg <- tagGen sk t;
    return tg;
  }
  proc getTagLog() :  Time list = {
    return lt;
  }
  proc getPK() : pkey = {
    return pk;
  }
}.


(* checkTagLog t l = true iff list l contains no element larger or equal than t  *)
op checkTagLog (t : Time, l : Time list) : bool =
 with l = [] => true
 with l = (x :: xs) => if x < t then checkTagLog t xs else false.


(* multiple-time forward-resistance game *)
module GameFR(A : AdvFR, T : TagOracleT, K : KeyGenT) = {
  module A = A(T)
  var i : Time
  var tg : tag option
  var sl : Time list
  proc main() : bool = {
    var pk, sk;
    (pk, sk) <@ K.keyGen();    
    T.init(pk, sk);
    (i, tg) <@ A.forge(pk);
    sl <@ T.getTagLog();
    return  0 < i /\ i <= EXP /\ tagVer pk i tg /\ checkTagLog i sl;
  }
}.

end TagSystem.
