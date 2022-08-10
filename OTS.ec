require import FSet Int Real SmtMap Distr.

abstract theory OTS_Theory.

(* types and functions associated with One-Time Signature Scheme *)
type pkey, skey, message, sig.

op otsSig : skey -> message -> sig.
op otsVer : pkey option -> message -> sig -> bool.
op otsKey : int -> pkey * skey.


require import KeyGen.
clone import KeyGen  with type pkey <- pkey,
                          type skey <- skey,
                          op   keyGen <- otsKey.


(* the OTS oracle module type *)                          
module type OTSOracleT = {
  proc init(pk : pkey, sk : skey) : unit
  proc sign(m : message) : sig option
  proc fresh(m : message) : bool
}.


(* The OTS adversaries with the access to the OTS oracle *)
module type AdvOTS (O : OTSOracleT) = {
  proc forge(pk : pkey) : message * sig {O.sign}
}.


(* OTS game which represents the existantial unforgeability under the
chosen message attack *)
module GameOTS(O : OTSOracleT, A : AdvOTS, K : KeyGenT) = {
  module A = A(O)
  var s : sig
  var m : message
  proc main() : bool = {
    var pk, sk, forged, fresh;
    (pk, sk) <@ K.keyGen();
    O.init(pk, sk);    
    (m, s) <@ A.forge(pk);
    forged  <- otsVer (Some pk) m s;
    fresh   <@ O.fresh(m);
    return forged /\ fresh;
  }
}.


(* The standard implementation of OTS oracle. Note that the oracle
will generate the signature for only one message. *)
module OTSOracle : OTSOracleT = {
  var qs   : message option
  var used : bool
  var pk : pkey
  var sk : skey  
  proc init(pk : pkey, sk : skey) : unit = {
    OTSOracle.pk   <- pk;
    OTSOracle.sk   <- sk;
    qs   <- None;
    used <- false;
  }
  proc sign(m : message) : sig option = {
    var r, q;
    if(!used){
      qs <- Some m;
      q <- otsSig sk m;
      r <- Some q;
    }else{
      r <- None;
    }
    used <- true;
    return r;
  }
  proc fresh(m : message) : bool = {
    return (Some m) <> qs;
  }
}.


end OTS_Theory.
