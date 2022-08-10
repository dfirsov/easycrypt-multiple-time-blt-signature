require import FSet Int Real SmtMap Distr List DInterval BasicProps.


(* Here we develop an auxiliary scheme where M one-time keypairs are
generated and adversary wins if they manage to forge a signature for
  at least one of the keypair. *)

abstract theory OTSM_Theory.

type pkey, skey, message, sig.
op otsKey : int -> pkey * skey.
op M : int.
op dR : int distr.
op otsSig : skey -> message -> sig.
op otsVer : pkey option -> message -> sig -> bool.
  

op otsSigMany : (int -> skey option) -> int -> message -> sig 
 = fun skf i m => otsSig (oget (skf i)) m.

 
op otsVerMany : (int -> pkey option) -> int -> message -> sig -> bool
 = fun pkf i m s => otsVer (pkf i) m s.



require IdealPRF.
clone export IdealPRF as NP with type D <- int,
                                 type R <- int,
                                 type K <- int,
                                 op dR <- dR,
                                 op dK <- dR.


require import KeyGen.
clone export KeyGen  with type pkey <- (int -> pkey option),
                          type skey <- (int -> skey option),
                            op dR <- dR.


module KeyGenOTSM (F : PRF_Hiding) : KeyGenT = {
  proc keyGen() : (int -> pkey option) * (int -> skey option) = {
     var pkf : (int -> pkey option);
     var skf : (int -> skey option);
     var i : int;
     var pk : pkey;
     var sk : skey;
     var rs : int;
     F.init();
     pkf <- fun _ => None;
     skf <- fun _ => None;
     i <- 1;
    while (i < M + 1){
      rs <@ F.f(i);
      (pk, sk) <- otsKey rs;
      pkf <- fun x => if x = i then Some pk else pkf x;
      skf <- fun x => if x = i then Some sk else skf x;
      i <- i + 1;
     }
    return (pkf, skf);
  }
}.


module OTSMKeysIdeal : KeyGenT = KeyGenOTSM (RandomFunction).


module type OTSMOracleT = {
  proc  init(pk : int -> pkey option, sk : int -> skey option) : unit
  proc sign(n : int, m : message) : sig option
  proc fresh(i : int, m : message) : bool
  proc getMsgLog() : (int, message) fmap
  proc getSigLog() : (int, sig) fmap
  proc getPK() : int -> pkey option
}.


module OTSMOracle = {
  var used : (int, unit) fmap
  var skf : int -> skey option
  var pkf : int -> pkey option
  var log : (int, message) fmap 
  var slog : (int, sig) fmap    
  proc init(pkf : int -> pkey option, skf : int -> skey option) = {
    OTSMOracle.skf <- skf;
    OTSMOracle.pkf <- pkf;
    used <- empty;
    log <- empty;
    slog <- empty;
  }
  proc sign(n : int, m : message) : sig option  = {
    var r;
    if(used.[n] = Some ()){
       r <- None;
    }else{
      r <- Some (otsSigMany skf n m);
      log <- log.[n <- m];
      slog <- slog.[n <- (otsSigMany skf n m)];
    }
    used <- used.[n <- ()];
    return r;
  }  
  proc fresh(i : int, m : message) : bool = {
    return (Some m) <> log.[i];
  }
  proc getSigLog() : (int , sig) fmap = {
    return slog;
  }
  proc getMsgLog() : (int , message) fmap = {
    return log;
  }
  proc getPK() : int -> pkey option = {
    return pkf;
  }

}.


module type AdvOTSM (O : OTSMOracleT) = {
  proc forge(pk : int -> pkey option) : int * message * sig {O.sign, O.getMsgLog ,
                                                             O.getSigLog, O.getPK}
}.


module GameOTSM(O : OTSMOracleT, A : AdvOTSM, K : KeyGenT) = {
  module A = A(O)
  var i : int
  var s : sig
  var m : message
  proc main() : bool = {
    var pk, sk, forged, fresh;
    (pk, sk) <@ K.keyGen();
    O.init(pk, sk);    
    (i, m, s) <@ A.forge(pk);
    forged  <- otsVerMany pk i m s;
    fresh   <@ O.fresh(i, m);
    return 0 < i /\ i <= M /\ forged /\ fresh;
  }
}.

end OTSM_Theory.
