require import Int Bool Distr AllCore List AllCore Array SmtMap.

(* The main goal of the developmen in this file is to establish the
equivalence of the output distributions of OTSMKeysIdeal and
OTSMKeysIdeal' keygenerators. Both keygenerators produce a tables of
public and secret keys, but the OTSMKeysIdeal' keygenerator resamples
the keypair in one of the cells of the table.

The final result is achieved by a serious of reductions and the
desired equivalence is expressed in the lemma idealKeyGenEquiv.
*)

require TagKeysEff.
clone export TagKeysEff as LEP.


module OTSMKeysIdeal'' (F : PRF_Hiding)  = {
  proc keyGen(p : int)  = {
     var pkf : (int -> pkey option);
     var skf : (int -> skey option);
     var i : int;
     var pk, pk0 : pkey;
     var sk, sk0 : skey;
     var rs, rs0 : int;
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
     rs0 <$ dR;
     (pk0, sk0) <- otsKey rs0;
     pkf <- fun x => if x = p then Some pk0 else  (pkf x);
     skf <- fun x => if x = p then Some sk0 else  (skf x);
    return (pkf, skf);
  }
}.

module OTSMKeysIdealZZ (F : PRF_Hiding)  = {
  proc keyGen(p : int)  = {
     var pkf : (int -> pkey option);
     var skf : (int -> skey option);
     var i : int;
     var pk, pk0 : pkey;
     var sk, sk0 : skey;
     var rs, rs0 : int;
     F.init();
     pkf <- fun _ => None;
     skf <- fun _ => None;
     i <- 1;
    while (i < M + 1){
      rs <$ dR;
      (pk, sk) <- otsKey rs;
      pkf <- fun x => if x = i then Some pk else pkf x;
      skf <- fun x => if x = i then Some sk else skf x;
      i <- i + 1;
     }
     rs0 <$ dR;
     (pk0, sk0) <- otsKey rs0;
     pkf <- fun x => if x = p then Some pk0 else  (pkf x);
     skf <- fun x => if x = p then Some sk0 else  (skf x);
    return (pkf, skf);
  }
}.


module OTSMKeysIdeal'  = OTSMKeysIdeal'' (RandomFunction).
module OTSMKeysIdealZ  = OTSMKeysIdealZZ (RandomFunction).

module OTSMKeysIdeal_0   = {

  proc keyGen(p : int)  = {
     var pkf : (int -> pkey option);
     var skf : (int -> skey option);
     var i : int;
     var pk : pkey;
     var sk : skey;
     var rs : int;
     RandomFunction.init();
     pkf <- fun _ => None;
     skf <- fun _ => None;
     i <- 1;
    while (i < M + 1){
      rs <$ dR;
      (pk, sk) <- otsKey rs;
      pkf <- fun x => if x = i then Some pk else pkf x;
      skf <- fun x => if x = i then Some sk else skf x;
      i <- i + 1;
     }
    return (pkf, skf);
  }
}.

module OTSMKeysIdeal_1   = {
  proc keyGen(p : int)  = {
     var pkf : (int -> pkey option);
     var skf : (int -> skey option);
     var i : int;
     var pk : pkey;
     var sk : skey;
     var rs : int;
     RandomFunction.init();
     pkf <- fun _ => None;
     skf <- fun _ => None;
     i <- 1;
    while (i < M + 1 /\ i < p){
      rs <$ dR;
      (pk, sk) <- otsKey rs;
      pkf <- fun x => if x = i then Some pk else pkf x;
      skf <- fun x => if x = i then Some sk else skf x;
      i <- i + 1;
     }
    while (i < M + 1){
      rs <$ dR;
      (pk, sk) <- otsKey rs;
      pkf <- fun x => if x = i then Some pk else pkf x;
      skf <- fun x => if x = i then Some sk else skf x;
      i <- i + 1;
     }
    return (pkf, skf);
  }
}.


module OTSMKeysIdeal_2   = {
  proc keyGen(p : int)  = {
     var pkf : (int -> pkey option);
     var skf : (int -> skey option);
     var i : int;
     var pk : pkey;
     var sk : skey;
     var rs : int;
     RandomFunction.init();
     pkf <- fun _ => None;
     skf <- fun _ => None;
     i <- 1;
    while (i < p){
      rs <$ dR;
      (pk, sk) <- otsKey rs;
      pkf <- fun x => if x = i then Some pk else pkf x;
      skf <- fun x => if x = i then Some sk else skf x;
      i <- i + 1;
     }
    while (i < M + 1){
      rs <$ dR;
      (pk, sk) <- otsKey rs;
      pkf <- fun x => if x = i then Some pk else pkf x;
      skf <- fun x => if x = i then Some sk else skf x;
      i <- i + 1;
     }
    return (pkf, skf);
  }
}.


module OTSMKeysIdeal_3   = {

  proc keyGen(p : int)  = {
     var pkf : (int -> pkey option);
     var skf : (int -> skey option);
     var i : int;
     var pk : pkey;
     var sk : skey;
     var rs : int;
     RandomFunction.init();
     pkf <- fun _ => None;
     skf <- fun _ => None;
     i <-  1;
    while (i < p){
      rs <$ dR;
      (pk, sk) <- otsKey rs;
      pkf <- fun x => if x = i then Some pk else pkf x;
      skf <- fun x => if x = i then Some sk else skf x;
      i <- i + 1;
     }
     rs <$ dR;
     (pk, sk) <- otsKey rs;
     pkf <- fun x => if x = p then Some pk else pkf x;
     skf <- fun x => if x = p then Some sk else skf x;
     i <- i + 1;
    while (i < M + 1){
      rs <$ dR;
      (pk, sk) <- otsKey rs;
      pkf <- fun x => if x = i then Some pk else pkf x;
      skf <- fun x => if x = i then Some sk else skf x;
      i <- i + 1;
     }
    return (pkf, skf);
  }
}.


module OTSMKeysIdeal_4   = {
  proc keyGen(p : int)  = {
     var pkf : (int -> pkey option);
     var skf : (int -> skey option);
     var i : int;
     var pk,pk0 : pkey;
     var sk,sk0 : skey;
     var rs, rs0 : int;
     RandomFunction.init();
     pkf <- fun _ => None;
     skf <- fun _ => None;
     i <- 1;
    while (i < p){
      rs <$ dR;
      (pk, sk) <- otsKey rs;
      pkf <- fun x => if x = i then Some pk else pkf x;
      skf <- fun x => if x = i then Some sk else skf x;
      i <- i + 1;
     }
     rs0 <$ dR;
     (pk0, sk0) <- otsKey rs0;
     pkf <- fun x => if x = p then Some pk0 else pkf x;
     skf <- fun x => if x = p then Some sk0 else skf x;
     i <- i + 1;
    while (i < M + 1){
      rs <$ dR;
      (pk, sk) <- otsKey rs;
      pkf <- fun x => if x = i then Some pk else pkf x;
      skf <- fun x => if x = i then Some sk else skf x;
      i <- i + 1;
     }
    return (pkf, skf);
  }
}.


module OTSMKeysIdeal_5   = {
  proc keyGen(p : int)  = {
     var pkf : (int -> pkey option);
     var skf : (int -> skey option);
     var i : int;
     var pk,pk0 : pkey;
     var sk,sk0 : skey;
     var rs, rs0 : int;
     RandomFunction.init();
     pkf <- fun _ => None;
     skf <- fun _ => None;
     i <- 1;
    while (i < p){
      rs <$ dR;
      (pk, sk) <- otsKey rs;
      pkf <- fun x => if x = i then Some pk else pkf x;
      skf <- fun x => if x = i then Some sk else skf x;
      i <- i + 1;
     }
     rs0 <$ dR;
     (pk0, sk0) <- otsKey rs0;
     pkf <- fun x => if x = p then Some pk0 else pkf x;
     skf <- fun x => if x = p then Some sk0 else skf x;
     i <- i + 1;
    while (i < M + 1){
      rs <$ dR;
      (pk, sk) <- otsKey rs;
      pkf <- fun x => if x = i then Some pk else pkf x;
      skf <- fun x => if x = i then Some sk else skf x;
      i <- i + 1;
     }
     pkf <- fun x => if x = p then Some pk0 else pkf x;
     skf <- fun x => if x = p then Some sk0 else skf x;
    return (pkf, skf);
  }
}.


module OTSMKeysIdeal_6   = {
  proc keyGen(p : int)  = {
     var pkf : (int -> pkey option);
     var skf : (int -> skey option);
     var i : int;
     var pk,pk0 : pkey;
     var sk,sk0 : skey;
     var rs, rs0 : int;
     RandomFunction.init();
     pkf <- fun _ => None;
     skf <- fun _ => None;
     i <- 1;
    while (i < p){
      rs <$ dR;
      (pk, sk) <- otsKey rs;
      pkf <- fun x => if x = i then Some pk else pkf x;
      skf <- fun x => if x = i then Some sk else skf x;
      i <- i + 1;
     }
     i <- i + 1;
    while (i < M + 1){
      rs <$ dR;
      (pk, sk) <- otsKey rs;
      pkf <- fun x => if x = i then Some pk else pkf x;
      skf <- fun x => if x = i then Some sk else skf x;
      i <- i + 1;
     }
     rs0 <$ dR;
     (pk0, sk0) <- otsKey rs0;
     pkf <- fun x => if x = p then Some pk0 else pkf x;
     skf <- fun x => if x = p then Some sk0 else skf x;
    return (pkf, skf);
  }
}.


module OTSMKeysIdeal_7   = {
  proc keyGen(p : int)  = {
     var pkf : (int -> pkey option);
     var skf : (int -> skey option);
     var i : int;
     var pk,pk0 : pkey;
     var sk,sk0 : skey;
     var rs, rs0 : int;
     RandomFunction.init();
     pkf <- fun _ => None;
     skf <- fun _ => None;
     i <- 1;
    while (i < M + 1){
      if(i <> p){
        rs <$ dR;
        (pk, sk) <- otsKey rs;
        pkf <- fun x => if x = i then Some pk else pkf x;
        skf <- fun x => if x = i then Some sk else skf x;
      }
      i <- i + 1;
     }
     rs0 <$ dR;
     (pk0, sk0) <- otsKey rs0;
     pkf <- fun x => if x = p then Some pk0 else pkf x;
     skf <- fun x => if x = p then Some sk0 else skf x;
    return (pkf, skf);
  }
}.


lemma l2_0 : 
 equiv [ OTSMKeysIdeal.keyGen ~ OTSMKeysIdeal_0.keyGen : 
    1 <= arg{2} /\ arg{2} <= M ==>  ={res}  ]. 
proof. proc. 
while (={skf,pkf,i} /\ (forall j, i{1} <= j => j \notin RandomFunction.m{1})).
wp.
inline*.
wp.
seq 1 0 : (={skf, pkf,i} /\ (forall j, i{1} <= j => j \notin RandomFunction.m{1}) /\ x{1} = i{1}). wp. skip. progress.
rcondt{1} 1. 
move => &1.
skip. progress. smt.
wp. rnd. skip. progress. smt. smt. smt.
wp.
inline*. wp. skip. progress.  smt.
qed.


lemma l2_1 : 
 equiv [ OTSMKeysIdeal_0.keyGen ~ OTSMKeysIdeal_1.keyGen : 
     ={arg} /\ 1 <= arg{2} /\ arg{2} <= M ==>  ={res}  ]. 
proof. proc. 
splitwhile {1} 5 : (i < p).
sim.
qed.


lemma l_3 : 
 equiv [ OTSMKeysIdeal_1.keyGen ~ OTSMKeysIdeal_2.keyGen : 
   arg{1} = arg{2} /\ 1 <= arg{1} /\ arg{1} <= M ==>  ={res}  ]. 
proof. proc. 
wp.
while (={skf,pkf,i,p, glob RandomFunction}).
wp. 
rnd. skip. progress. 
while (={skf,pkf,i,p, glob RandomFunction} /\ p{1} < M + 1).
wp. rnd. skip. progress.  smt. wp. inline*. wp.  skip. progress. smt.
smt.
qed.


lemma l4' : 
 equiv [ OTSMKeysIdeal_2.keyGen ~ OTSMKeysIdeal_3.keyGen : 
   ={arg} /\ 1 <= arg{1} /\ arg{1} <= M ==>  ={res}  ]. 
proc. unroll {1} 6. rcondt {1} 6.
move => &1. while (p < M + 1 /\ i <= p).
wp.   rnd. skip. progress.   smt.  inline*. wp.  skip. progress. smt. smt. sim. 
while (={skf,pkf,i,p, glob RandomFunction} /\ p{1} < M + 1 /\ i{1} <= p{1}).
wp. rnd. skip. progress.
smt. wp.  inline*.  wp.  skip. progress. smt. smt.
qed.


lemma l5' : 
 equiv [ OTSMKeysIdeal_3.keyGen ~ OTSMKeysIdeal_4.keyGen : 
   arg{1} = arg{2} /\ 1 <= arg{1} /\ arg{1} <= M ==>  ={res}  ]. 
proof. proc. sim. 
qed.


lemma l6' : 
 equiv [ OTSMKeysIdeal_4.keyGen ~ OTSMKeysIdeal_5.keyGen : 
   arg{1} = arg{2} /\ 1 <= arg{1} /\ arg{1} <= M ==>  ={res}  ]. 
proof. proc.  wp.
seq  5 5 : (={ pkf, skf, i,  p} /\ p{1} <= i{1} ).
while (={ pkf, skf, i,  p} /\ i{1} <= p{1}  ). wp.
rnd. skip. progress.
smt.
wp.  inline*. wp. skip. progress. smt.
seq 5 5 : (={pk0, sk0, pkf, skf, i, rs0, p} /\ (pkf{1} p{1} = Some pk0{1} ) 
  /\ (skf{1} p{1} = Some sk0{1} ) /\  ((pk0,sk0) = otsKey rs0){2} /\ p{1} < i{1}).
wp. rnd.
skip. progress.
smt. 
smt. 
while ((={pk0, sk0, pkf, skf, i, rs0, p} /\ (pkf{1} p{1} = Some pk0{1} ) 
  /\ (skf{1} p{1} = Some sk0{1} )) /\ ((pk0,sk0) = otsKey rs0){2} /\ p{1} < i{1} ).
wp.  inline*. wp.
rnd. skip.
progress. smt. smt. smt.
skip.
progress. smt. smt.
qed.


lemma l7' : 
 equiv [ OTSMKeysIdeal_5.keyGen ~ OTSMKeysIdeal_6.keyGen : 
   arg{1} = arg{2} /\ 1 <= arg{1} /\ arg{1} <= M ==>  ={res}  ]. 
proc.  swap {2} 8 -2. swap {2} 9 -2. swap {1} 10 -2.
seq 8 8 : (={rs0,pk0,sk0, skf, pkf,i,p} /\ p{1} < i{1}).
wp. rnd.
while (={skf, pkf,i,p} /\ i{1} <= p{1}).
wp. rnd. skip.  progress. smt. wp.  inline*. wp. skip. progress. smt.
wp.  
while (={i,p} /\ p{1} < i{1} /\ (forall i, i <> p{1} => skf{1} i = skf{2} i) 
  /\ (forall i, i <> p{1} => pkf{1} i = pkf{2} i) /\ (pkf p = Some pk0){1} /\ (skf p = Some sk0){1} ).
wp.  rnd. skip. progress. smt. smt. smt. smt. smt. wp. skip. progress. smt.
smt.  smt.  smt.
qed.


lemma l8' : 
 equiv [ OTSMKeysIdeal_6.keyGen ~ OTSMKeysIdeal_7.keyGen : 
   arg{1} = arg{2} /\ 1 <= arg{1} /\ arg{1} <= M ==>  ={res}  ]. 
proc. splitwhile {2} 5 : (i < p).
seq 5 5 : (={i,skf, pkf, p} /\ i{1} = p{1} /\ p{1} <= M).
while (={i,skf, pkf, p} /\ i{1} <= p{1} /\ p{1} <= M).
rcondt {2} 1.
move => &1. skip. progress. smt.
wp.
rnd. 
progress.
skip.  progress. smt. smt.
wp. 
inline*. wp. skip. progress. smt. smt. 
unroll {2} 1.
rcondt {2} 1.
move => &1. skip. progress. smt.
rcondf {2} 1.
move => &1. skip. progress. 
wp.
rnd. 
while (={skf, pkf, i, p} /\ p{1} < i{1}).
rcondt {2} 1.
move => &1. skip. progress. smt.
wp.
rnd.
skip. 
progress.
smt.
wp. 
skip. 
progress.
smt.
qed.


lemma limp : 
 equiv [ OTSMKeysIdeal_7.keyGen  ~ OTSMKeysIdealZ.keyGen :
   arg{1} = arg{2} /\ 1 <= arg{1} /\ arg{1} <= M ==>  ={res}  ]. 
proc. symmetry.
seq 5 5 : (={p} /\ (forall i, i <> p{1} => skf{1} i = skf{2} i) 
  /\ (forall i, i <> p{1} => pkf{1} i = pkf{2} i) ).
wp. while ((={p,i} /\ (forall i, i <> p{1} => skf{1} i = skf{2} i) 
  /\ (forall i, i <> p{1} => pkf{1} i = pkf{2} i) )).
if {2}. wp. inline*. wp. 
rnd.
skip. progress.
smt. 
smt. 
wp. rnd{1}.
skip. progress.  smt. smt. smt.
wp. inline*. wp.  
progress.  
wp. rnd. skip. progress. smt. smt.
qed.
 

lemma limpO : 
 equiv [ OTSMKeysIdealZ.keyGen  ~ OTSMKeysIdeal'.keyGen : ={arg} ==> ={res} ].
proof. proc.
wp.  rnd.
while (={p,skf,pkf,i} /\ (forall j, i{2} <= j => j \notin RandomFunction.m{2})).
wp.
inline*.
wp.
seq 0 1 : (={p,skf, pkf,i} 
   /\ (forall j, i{2} <= j => j \notin RandomFunction.m{2}) 
   /\ x{2} = i{2}). 
wp. skip. progress. 
rcondt{2} 1. 
move => &1.
skip. progress. smt. wp.
rnd. skip. progress. smt. smt. smt.
wp.
inline*. wp. skip. progress.  smt.
qed.


lemma idealKeyGenEquiv : 
 equiv [ OTSMKeysIdeal.keyGen 
          ~ OTSMKeysIdeal'.keyGen 
          : 1 <= arg{2} /\ arg{2} <= M  ==> ={res} ].
transitivity OTSMKeysIdeal_0.keyGen 
    (1 <= arg{2} /\ arg{2} <= M  ==> ={res})
    (={arg} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res}). smt. auto. 
apply l2_0.
transitivity OTSMKeysIdeal_1.keyGen 
    (={p} /\ 1 <= arg{2} /\ arg{2} <= M  ==> ={res})
    (={p} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res}). smt. auto. 
apply l2_1.
transitivity OTSMKeysIdeal_2.keyGen 
    (={p} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res})
    (={p} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res}). smt. auto. 
apply l_3.
transitivity OTSMKeysIdeal_3.keyGen 
    (={p} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res})
    (={p} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res}). smt. auto. 
apply l4'.
transitivity OTSMKeysIdeal_4.keyGen 
    (={p} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res})
    (={p} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res}). smt. auto. 
apply l5'.
transitivity OTSMKeysIdeal_5.keyGen 
    (={p} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res})
    (={p} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res}). smt. auto. 
apply l6'.
transitivity OTSMKeysIdeal_6.keyGen 
    (={p} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res})
    (={p} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res}). smt. auto. 
apply l7'.
transitivity OTSMKeysIdeal_7.keyGen 
    (={p} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res})
    (={p} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res}). smt. auto. 
apply l8'.
transitivity OTSMKeysIdealZ.keyGen 
    (={p} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res})
    (={p} /\ 1 <= arg{1} /\ arg{1} <= M  ==> ={res}). smt. auto. 
apply limp.
conseq (limpO).
auto.
qed.



