require import Int Bool Distr DInterval List SmtMap Real BasicProps.

(* The main goal of the auxiliary development in this file is to
establish that the probability of breaking M one-time signatures is
upper bounded by 1/M * probability of breaking a single one-time
signature.

The desired result is derived in lemma otsm2otsUB. *)

require OTSMKeys.
clone export OTSMKeys as KGP.


module OWrapper(O : OTSOracleT) = {
  var p : int
  proc init(pkf : int -> pkey option, skf : int -> skey option) = {
    OTSMOracle.init(pkf, skf);
  }  
  proc sign(n : int, m : message) : sig option  = {
    var r ;
    r <@ OTSMOracle.sign(n,m);    
    if (n = p){
      r <@ O.sign(m); 
      if(r <> None){
        OTSMOracle.slog <- OTSMOracle.slog.[n <- oget r];
      }
    }    
    return r;
  }  
  proc fresh(i : int, m : message) : bool = {
    var r;
    r <@ OTSMOracle.fresh(i, m);
    return r;
  }
  proc getSigLog() = {
    var r;
    r <@ OTSMOracle.getSigLog();
    return r;
  }
  proc getMsgLog() = {
    var r;
    r <@ OTSMOracle.getMsgLog();
    return r;
  }
  proc getPK() = {
    var r;
    r <@ OTSMOracle.getPK();
    return r;
  }  
}.


module Wrapper0(A : AdvOTSM, O : OTSOracleT) = {
  module W = OWrapper(O)
  module A = A(W)
  var p : int
  proc forge(pk:pkey) : message * sig = {
    var r1, r2, r3, pkf, skf;
   p <$ dinter 1 M;
   (pkf, skf) <@ OTSMKeysIdeal.keyGen();
   pkf <- fun x => if x = p then Some pk else  (pkf x);
   W.init(pkf, skf);
   OWrapper.p <- p;   
   (r1, r2, r3) <@ A.forge(pkf);    
   return (r2, r3);
  }
}.


module WrapperP(A : AdvOTSM, O : OTSOracleT) = {
  module A = A(OTSMOracle)
  var p : int
  proc forge(pk:pkey) : message * sig = {
   var r1, r2, r3, pkf, skf;
   p <$ dinter 1 M;
   (pkf, skf) <@ OTSMKeysIdeal.keyGen();
   pkf <- fun x => if x = p then Some pk else  (pkf x);
   OTSMOracle.init(pkf, fun x => if x = p then Some OTSOracle.sk else  (skf x));
   (r1, r2, r3) <@ A.forge(pkf);
   OTSOracle.qs <- OTSMOracle.log.[p];
   return (r2, r3);
  }
}.


module Wrapper'(A : AdvOTSM, O : OTSOracleT) = {
  module A = A(OTSMOracle)
  var p : int
  proc forge() : pkey option * message * sig = {
   var r1, r2, r3, pkf, skf, p;
   p <$ dinter 1 M;
   (pkf, skf) <@ OTSMKeysIdeal'.keyGen(p);
   OTSMOracle.init(pkf, skf);
   (r1, r2, r3) <@ A.forge(pkf);
   OTSOracle.qs <- OTSMOracle.log.[p];    
   return (pkf p, r2, r3);
  }
}.


module Wrapper''(A : AdvOTSM, O : OTSOracleT) = {
  module A = A(OTSMOracle)
  var p : int
  proc forge() : pkey option * message * sig = {
   var r1, r2, r3, pkf, skf;
   (pkf, skf) <@ OTSMKeysIdeal.keyGen();
   OTSMOracle.init(pkf, skf);
   (r1, r2, r3) <@ A.forge(pkf);
   p <$ dinter 1 M;
   OTSOracle.qs <-  OTSMOracle.log.[p];    
   return (pkf p, r2, r3);
  }
}.


module type AdvOTS' (O : OTSOracleT) = {
  proc forge() : pkey option * message * sig {O.sign}
}.


module GameOTS'(O : OTSOracleT, A : AdvOTS') = {
  module A = A(O)
  var s : sig
  var m : message
  proc main() : bool = {
    var pk, forged, fresh;
    OTSOracle.qs <- None;
    OTSOracle.used <- false;
    (pk, m, s) <@ A.forge();
    forged  <- otsVer pk m s;
    fresh   <@ O.fresh(m);
    return forged /\ fresh;
  }
}.


module GameOTSMP(O : OTSMOracleT, A : AdvOTSM) = {
  module A = A(O)
  var i : int
  var s : sig
  var m : message
  var p : int
  proc main() : bool = {
    var pk, sk, forged, fresh;
    (pk, sk) <@ OTSMKeysIdeal.keyGen();
    O.init(pk, sk);    
    (i, m, s) <@ A.forge(pk);
    forged  <- otsVerMany pk i m s;
    fresh   <@ O.fresh(i, m);
    p <$ dinter 1 M;    
    return 0 < i /\ i <= M /\ forged /\ fresh;
  }
}.


module GameOTSMP''(O : OTSMOracleT, A : AdvOTSM) = {
  module A = A(O)
  var i : int
  var s : sig
  var m : message
  var p : int
  proc main() : bool = {
    var pk, sk, forged, fresh;
    (pk, sk) <@ OTSMKeysIdeal.keyGen();
    O.init(pk, sk);    
    (i, m, s) <@ A.forge(pk);
    forged  <- otsVerMany pk i m s;
    fresh   <@ O.fresh(i, m);    
    return 0 < i /\ i <= M /\ forged /\ fresh;
  }
}.


module GameOTSMP'(O : OTSMOracleT, A : AdvOTSM) = {
  module G = GameOTSMP''(O, A)
  var p : int
  var r : bool
  proc main() : bool = {
    r <@ G.main();
    p <$ dinter 1 M;    
    return r;
  }
}.


section.

declare module A <: AdvOTSM{-OTSMOracle, -OTSOracle, -WrapperP,  -Wrapper', -Wrapper'', 
                              -OWrapper, -Wrapper0, -GameOTSMP', -GameOTSMP'', -RandomFunction}.

axiom sl : forall (O <: OTSMOracleT{-A}), islossless O.sign => islossless O.getSigLog =>
    islossless O.getMsgLog =>
    islossless O.getPK => islossless A(O).forge.



lemma sll i  f x r : otsVerMany f i x r => otsVer (f i) x r by auto.
lemma gen1 skf p sk m : skf p = Some sk => otsSig sk m = otsSigMany skf p m. admitted.
lemma dda z : z \in dinter 1 M => z <= M by smt.
lemma ddb z : z \in dinter 1 M => 0 <= z by smt.           

    
lemma signEq : equiv [ OTSMOracle.sign ~ OTSMOracle.sign : 
  ={glob OTSMOracle, glob RandomFunction, n, m} ==> ={res, glob OTSMOracle} ]. 
proc. sim. qed.


lemma opspr' &m : phoare[ GameOTSMP''(OTSMOracle, A).main : 
    (glob A) = (glob A){m} 
 /\ (glob OTSMOracle) = (glob OTSMOracle){m} 
 /\ (glob RandomFunction) = (glob RandomFunction){m}  ==> res 
 /\ (res => GameOTSMP''.i <= M /\ 1 <= GameOTSMP''.i) ] 
 = Pr[ GameOTSMP(OTSMOracle, A).main() @ &m : res ].
bypr. move => &m0 b. byequiv.
proc. inline*.
wp. rnd {2}. wp. call(_: ={glob OTSMOracle, glob RandomFunction}).
conseq signEq;auto. 
sim. sim. sim. wp.
while (={i,pkf,skf, glob RandomFunction}).
wp. 
seq 1 1 : (={x,i, pkf, skf, glob RandomFunction} /\ i{1} < M + 1 /\ i{2} < M + 1).
wp. skip. progress.
if. auto. wp. rnd. skip. progress. skip. progress.
wp. skip. progress;smt. auto. auto.
qed.


lemma ch3pr' &m : 
   Pr[ GameOTSMP'(OTSMOracle, A).main() @ &m : GameOTSMP'.p = GameOTSMP''.i  /\ res ] 
 = Pr[ GameOTSMP(OTSMOracle, A).main() @ &m : GameOTSMP.p = GameOTSMP.i  /\ res].
byequiv (_ : ={glob A, glob OTSMOracle, glob RandomFunction} ==> _).
proc. inline*. wp. rnd. wp.
call(_: ={glob OTSMOracle, glob RandomFunction}).
conseq signEq;auto. 
sim. sim. sim. wp. 
while (={i,pkf,skf, glob RandomFunction}). wp.
seq 1 1 : (={x,i, pkf, skf, glob RandomFunction} /\ i{1} < M + 1 /\ i{2} < M + 1).
wp. skip. progress.
if. auto. wp. rnd. skip. progress. skip. progress.
wp. skip.  progress.  progress. progress.
qed.


lemma ch3pr &m : 
   Pr[ GameOTSMP'(OTSMOracle, A).main() @ &m : GameOTSMP'.p = GameOTSMP''.i /\ res ] 
 = (1%r / M%r) * Pr[ GameOTSMP(OTSMOracle, A).main() @ &m : res ].
proof. 
byphoare (_: (glob A) = (glob A){m} /\ (glob OTSMOracle) = (glob OTSMOracle){m} 
          /\ (glob RandomFunction) = (glob RandomFunction){m} ==> _ ).
proc*. inline GameOTSMP'(OTSMOracle, A).main. 
seq 1 :
  (GameOTSMP'.r /\ (GameOTSMP'.r => GameOTSMP''.i <= M /\ 1 <= GameOTSMP''.i{hr})) 
  Pr[ GameOTSMP(OTSMOracle, A).main() @ &m : res  ] 
  (1%r / M%r) 
  (1%r - Pr[ GameOTSMP(OTSMOracle, A).main() @ &m : res ]) 
  0%r.
inline*. wp. call (_:true).
proc. wp. skip. auto.
proc. auto. auto. auto.
wp. wp. while true.
wp. seq  1 : (i < M + 1).
wp. skip. progress.
if. wp. rnd. skip. progress. skip. progress.
wp. skip. progress.
call (opspr' &m). skip. progress.
wp.  rnd.  skip.  progress. rewrite H. simplify. 
have : GameOTSMP''.i{hr} <= M. smt.
have : 1 <= GameOTSMP''.i{hr}. smt.
move => h1 h2.
apply (ddi' GameOTSMP''.i{hr} M h2 h1).
wp. rnd. skip. smt. auto. auto. auto.
qed.


lemma gomp &m : 
   Pr[ GameOTSMP(OTSMOracle, A).main() @ &m : GameOTSMP.p = GameOTSMP.i /\ res ] 
 = (1%r / M%r) * Pr[ GameOTSMP(OTSMOracle, A).main() @ &m : res ].
rewrite - (ch3pr' &m).
apply (ch3pr &m).
qed.


lemma tr : 
 equiv [ GameOTSMP(OTSMOracle, A).main ~ GameOTS'(OTSOracle, Wrapper''(A)).main : 
    ={glob OTSMOracle, glob A, glob RandomFunction} 
 ==> (GameOTSMP.p{1} = GameOTSMP.i{1}) /\ res{1} => res{2} ].
proof. proc.
inline*. wp. rnd. wp.
call(_: ={glob OTSMOracle, glob RandomFunction}).
conseq signEq;auto. progress.
sim. sim. sim. wp.
wp. while (={i, glob RandomFunction} /\ pkf{1} = pkf0{2} /\ skf{1} = skf0{2}).
wp. 
seq 1 1 : (={x, i, glob RandomFunction} /\ pkf{1} = pkf0{2} /\ skf{1} = skf0{2} 
              /\ i{1} < M + 1 /\ i{2} < M + 1).
wp. skip. progress.
if. progress. wp. rnd. skip. progress. skip. progress.
wp. skip. progress. 
qed.


lemma pp &m : Pr[ GameOTSMP(OTSMOracle, A).main() @ &m : res ] 
 = Pr[ GameOTSM(OTSMOracle, A, OTSMKeysIdeal).main() @ &m : res ].
proof. byequiv (_ : ={glob A, glob OTSMOracle, glob RandomFunction} ==> _). proc. inline*.
wp. rnd {1}. wp.
call(_: ={glob OTSMOracle, glob RandomFunction}).
conseq signEq;auto. 
sim. sim. sim. wp. 
wp. while (={i,pkf,skf, glob RandomFunction}).
wp. 
seq 1 1 : (={x,i, pkf, skf, glob RandomFunction} /\ i{1} < M + 1 /\ i{2} < M + 1).
wp. skip. progress.
if. progress.
wp. rnd. skip. progress.
skip. progress. wp. skip. progress. smt.
auto. auto.
qed.


lemma qq &m : 
 Pr[ GameOTSMP(OTSMOracle, A).main() @ &m : GameOTSMP.p = GameOTSMP.i /\ res ]
  <= Pr[ GameOTS'(OTSOracle, Wrapper''(A)).main() @ &m : res ].
proof. byequiv (_ : ={glob A, glob OTSMOracle, glob RandomFunction} ==> _). 
conseq tr. auto. progress. smt.
qed.


lemma l0 &m : Pr[ GameOTS(OTSOracle, Wrapper0(A), K.SimpleKeyGen).main() @ &m : res ]
  = Pr[ GameOTS(OTSOracle, WrapperP(A), K.SimpleKeyGen).main() @ &m : res ].
proof. byequiv.
proc. inline*. wp.
call (_: WrapperP.p{2} \in dinter 1 M
 /\ OWrapper.p{1} = WrapperP.p{2}
 /\ (Some OTSOracle.sk{1}) = (OTSMOracle.skf WrapperP.p){2}
 /\ (((OTSMOracle.used{2}.[OWrapper.p{1}])) = Some ()) = OTSOracle.used{1}
 /\ (forall i, OTSMOracle.used.[i]{1} = OTSMOracle.used.[i]{2} )
 /\ (forall i, i <> OWrapper.p{1} => OTSMOracle.skf{1} i = OTSMOracle.skf{2} i)
 /\ (OTSMOracle.skf{2} WrapperP.p{2} = Some OTSOracle.sk{2})
 /\ ={OTSMOracle.log, OTSMOracle.slog, OTSMOracle.pkf}
 /\ OTSMOracle.log.[OWrapper.p]{1} = OTSOracle.qs{1}).
proc. inline*. wp. skip.
progress;smt. 
proc. inline*. wp.
skip. progress.
proc. inline*. wp. skip. progress.
proc. inline*. wp. skip. progress.
wp. while (={i,skf0,pkf0, glob RandomFunction}).
wp. 
seq 1 1 : ((={x, i, glob RandomFunction, skf0, pkf0}) /\
  i{1} < M + 1 /\ i{2} < M + 1).
wp. skip. progress.
if. progress. wp. rnd. skip. progress. skip. progress.
wp. rnd. wp. rnd.
skip. progress. smt. smt. 
have : pL <= M. smt.
smt.
auto. 
auto.
qed.


lemma l1 &m : Pr[ GameOTS(OTSOracle, WrapperP(A), K.SimpleKeyGen).main() @ &m : res ]
 = Pr[ GameOTS'(OTSOracle, Wrapper'(A)).main() @ &m : res ].
proof. byequiv (_: ={glob A,  glob RandomFunction} ==> _).
proc. inline*. swap {2} 10 -9. swap {2} 11 -9. wp.
call(_: ={glob OTSMOracle, glob RandomFunction}).
conseq signEq;auto. 
sim. sim. sim. wp. 
while (={i,skf0,pkf0, glob RandomFunction}). wp. 
seq 1 1 : (={x, i, skf0, pkf0, glob RandomFunction} /\ i{1} < M + 1 /\ i{2} < M + 1).
wp. skip. progress. if. progress. wp. rnd. skip. progress. skip. progress.
wp. rnd. wp. rnd. skip. progress. smt. auto.
qed.


lemma l2 &m : Pr[ GameOTS'(OTSOracle, Wrapper'(A)).main() @ &m : res ]
 = Pr[ GameOTS'(OTSOracle, Wrapper''(A)).main() @ &m : res ].
proof. byequiv (_: ={glob A, glob OTSOracle, glob OTSMOracle, glob RandomFunction} ==> _).
proc.
inline GameOTS'(OTSOracle, Wrapper'(A)).A.forge.
inline GameOTS'(OTSOracle, Wrapper''(A)).A.forge.
swap {2} 6 -3.
seq 3 3 : (={ glob OTSOracle, glob A} /\ p{1} = Wrapper''.p{2} /\ p{1} <= M /\ 1 <= p{1}) .
rnd. wp. skip.  progress. smt. smt.
seq 1 1 : (={skf, pkf, glob OTSOracle, glob A} /\ p{1} = Wrapper''.p{2} /\ p{1} <= M).
symmetry.
call idealKeyGenEquiv.
skip. progress. 
inline*. wp. 
call(_: ={glob OTSMOracle}).
sim. sim.
progress. sim. sim.
wp. skip.
progress. auto. auto.
qed.


lemma otsm2otsUB &m : Pr[ GameOTSM(OTSMOracle, A, OTSMKeysIdeal).main() @ &m : res ]  
 <= M%r * Pr[ GameOTS(OTSOracle, Wrapper0(A), K.SimpleKeyGen).main() @ &m : res ].
proof. rewrite - (pp &m).
have : M%r * Pr[GameOTSMP(OTSMOracle, A).main() @ &m : GameOTSMP.p = GameOTSMP.i /\ res]
 =  Pr[ GameOTSMP(OTSMOracle, A).main() @ &m : res ].
rewrite (gomp &m). smt.
move => h. rewrite - h.
have : Pr[GameOTSMP(OTSMOracle, A).main() @ &m :
   GameOTSMP.p = GameOTSMP.i /\ res] <=
Pr[GameOTS(OTSOracle, Wrapper0(A), K.SimpleKeyGen).main() @ &m : res].
rewrite (l0 &m).
rewrite (l1 &m).
rewrite (l2 &m).
apply (qq &m).
move => h2.
timeout 30. smt.
qed.


end section.
