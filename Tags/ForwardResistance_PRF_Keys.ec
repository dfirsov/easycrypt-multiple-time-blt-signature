require import Int Bool Real SmtMap Distr List BasicProps.

(* The main goal of this development is to prove that the probability
of breaking the multiple-time forward-resistance for the efficiently
("lazily") PRF based generated keypairs is upper bounded by the sum of
indistinguishability of the PRF and the expiration time times the
probability of breaking the unforgeability of the underlying OTS.

The main result is derived in lemma fr2otsAndPRFUB.
*)


require ForwardResistance_Independent_Keys.
clone export ForwardResistance_Independent_Keys as O2.


module BinaryStuff(O:OTSMOracleT) = {
  proc tag(t:int) = {
    var xs, ys : int list;
    var y : int;
    var r : tag option;
    var pkf : int -> pkey option;
    var slog : (int, sig) fmap;
    if(t <= 0){
      r <- None;
    }else{
      pkf <@ O.getPK();
      xs <- [];
      ys <- binRec t;
      while(ys <> []){
        y <- head witness ys;
        O.sign(y, (msg pkf y));
        xs <- xs ++ [y];
        ys <- behead ys;
      }
      slog <@ O.getSigLog();
      r <- (Some (tagGenS pkf slog (binRec t)));
    }
    return r;
  }
  proc init(pk : pkey, skf : int -> skey option) = {}
  proc pks (pkf : int -> pkey option)   : unit  = {}
  proc getTagLog() : int list  = {
    return [];
  }
}.



lemma constr : equiv[ TagOracle.tag ~ BinaryStuff(OTSMOracle).tag :
            TagOracle.sk{1} = OTSMOracle.skf{2} /\
            (forall (i : int),
               OTSMOracle.pkf{2} i =
               omap sk2pk (OTSMOracle.skf{2} i)) /\
            ={t} /\
            (forall (i : int) (m : message),
               OTSMOracle.log{2}.[i] = Some m =>
               exists (j : int), i <= j /\ (j \in TagOracle.lt{1})) /\
            (forall (i : int) (m : message),
               OTSMOracle.log{2}.[i] = Some m =>
               m = msg OTSMOracle.pkf{2} i) /\
            (forall (i : int),
               OTSMOracle.used{2}.[i] = Some tt =>
               OTSMOracle.slog{2}.[i] <> None) /\
            forall (i : int) (s : sig),
              OTSMOracle.slog{2}.[i] = Some s =>
              s =
              otsSigMany OTSMOracle.skf{2} i (msg OTSMOracle.pkf{2} i) ==>
            ={res} /\
            (forall (i : int) (m : message),
               OTSMOracle.log{2}.[i] = Some m =>
               exists (j : int), i <= j /\ (j \in TagOracle.lt{1})) /\
            (forall (i : int) (m : message),
               OTSMOracle.log{2}.[i] = Some m =>
               m = msg OTSMOracle.pkf{2} i) /\
            (forall (i : int) (s : sig),
               OTSMOracle.slog{2}.[i] = Some s =>
               s =
               otsSigMany OTSMOracle.skf{2} i (msg OTSMOracle.pkf{2} i)) /\
            forall (i : int),
              OTSMOracle.used{2}.[i] = Some tt =>
              OTSMOracle.slog{2}.[i] <> None].
proof. proc.
case (t{2} <= 0).
rcondt {2} 1.
move => &1. skip. progress.
wp. skip. progress. smt.   smt.
rcondf {2} 1. 
move => &1. skip. progress. 
seq 1 0 : (TagOracle.sk{1} = OTSMOracle.skf{2} 
   /\ (forall (i0 : int),
      OTSMOracle.pkf{2} i0 = omap sk2pk (OTSMOracle.skf{2} i0)) 
   /\ ={t} 
   /\ (forall (i0 : int) (m : message),
      OTSMOracle.log{2}.[i0] = Some m =>
      exists (j : int), i0 <= j /\ (j \in TagOracle.lt{1})) 
   /\ (forall (i0 : int) (m : message),
      OTSMOracle.log{2}.[i0] = Some m => m = msg OTSMOracle.pkf{2} i0)
   /\ (forall i,  OTSMOracle.used{2}.[i] = Some () => OTSMOracle.slog{2}.[i] <> None)
   /\ (forall (i0 : int) (s : sig),
      OTSMOracle.slog{2}.[i0] = Some s =>
      s = otsSigMany OTSMOracle.skf{2} i0 (msg OTSMOracle.pkf{2} i0)) 
   /\ (forall (i0 : int) (m : message),
     OTSMOracle.log{2}.[i0] = Some m =>
     exists (j : int), i0 <= j /\ (j \in TagOracle.lt{1})) 
   /\ (!t{2} <= 0) 
   /\ t{2} \in TagOracle.lt{1}).
wp. skip. progress;smt.
seq 0 4 : ((forall i s, OTSMOracle.slog.[i] = Some s 
      => s = otsSigMany OTSMOracle.skf i (msg OTSMOracle.pkf i)){2} 
   /\ (forall (j : int), j \in binRec t{2} => oget OTSMOracle.slog{2}.[j] =
         otsSig (oget (OTSMOracle.skf{2} j)) (msg OTSMOracle.pkf{2} j)){2} 
   /\ TagOracle.sk{1} = OTSMOracle.skf{2} 
   /\ (forall i, OTSMOracle.pkf{2} i =  omap sk2pk (OTSMOracle.skf{2} i))  
   /\ ={t} 
   /\ t{2} <= 0 = false 
   /\ (t{1} \in TagOracle.lt{1}) 
   /\ (forall i m, OTSMOracle.log.[i] = Some m => m = msg OTSMOracle.pkf i){2} 
   /\ (forall i,   OTSMOracle.used{2}.[i] = Some () => OTSMOracle.slog{2}.[i] <> None) 
   /\ (forall (i0 : int) (m : message),
         OTSMOracle.log{2}.[i0] = Some m =>
          exists (j : int), i0 <= j /\ (j \in TagOracle.lt{1}))
   /\ pkf{2} = OTSMOracle.pkf{2}).
while {2} (pkf{2} = OTSMOracle.pkf{2} 
  /\ (forall i s, OTSMOracle.slog.[i] = Some s 
        => s = otsSigMany OTSMOracle.skf i (msg OTSMOracle.pkf i)){2} 
  /\ (forall (j : int), j \in xs{2} => oget OTSMOracle.slog{2}.[j] =
     otsSig (oget (OTSMOracle.skf{2} j)) (msg OTSMOracle.pkf{2} j)) 
  /\ TagOracle.sk{1} = OTSMOracle.skf{2} 
  /\ (forall i,  OTSMOracle.pkf{2} i =  omap sk2pk (OTSMOracle.skf{2} i)) 
  /\ ={t}  
  /\ t{2} <= 0 = false 
  /\ (forall i m, OTSMOracle.log.[i] = Some m => m = msg OTSMOracle.pkf i){2}
  /\ (forall i,   OTSMOracle.used{2}.[i] = Some () => OTSMOracle.slog{2}.[i] <> None)
  /\ (t{1} \in TagOracle.lt{1}) /\ (forall (i0 : int) (m : message),
     OTSMOracle.log{2}.[i0] = Some m =>
     exists (j : int), i0 <= j 
  /\ (j \in TagOracle.lt{1})) 
  /\ (xs ++ ys = (binRec t)){2}) (size ys{2}).
move => &1 z.
inline*. wp. skip. progress.
have : exists y ys', ys{hr} = y :: ys'. smt (oa2). 
elim. move => y ys' pr.
case : (j \in xs{hr}).
move => ass1. smt.
move => ass1.
have : j = (head witness ys{hr}). timeout 30. smt.
move => ass2. rewrite ass2.
have : exists s, OTSMOracle.slog{hr}.[head witness ys{hr}] = Some s.
smt (oa2).
elim. move => s sp1. rewrite sp1.
simplify oget.
apply H. apply sp1.
smt. 
smt. 
have : exists y ys', ys{hr} = y :: ys'. smt (oa2). 
elim. move => y ys' pr. rewrite pr.
simplify. smt.
case : (i = head witness ys{hr}).
move => ass1. rewrite ass1. smt.
move => ass1. smt.
case : (j = head witness ys{hr}).
move => ass1. rewrite ass1. timeout 20. smt.
move => ass1. smt.
case : (i = head witness ys{hr}).
move => ass1. rewrite ass1. smt.
move => ass1. smt.
case : (i = head witness ys{hr}).
move => ass1. rewrite ass1. smt.
move => ass1. smt.
case : (i0 = head witness ys{hr}).
move => ass1. rewrite ass1. 
exists t{hr}.
have : exists y ys', ys{hr} = y :: ys'. smt (oa2). 
elim. move => y ys' pr. rewrite pr. simplify. progress.
have : y <= t{hr} /\ 0 < y.
apply br3. rewrite - H7. rewrite pr. smt. 
smt.
move => ass1. apply (H6 i0 (msg OTSMOracle.pkf{hr} i0)). smt.
smt.
have : exists y ys', ys{hr} = y :: ys'. smt (oa2). 
elim. move => y ys' pr. rewrite pr.
simplify. smt.
inline*. wp. skip.
progress. smt. smt. smt.
inline*. wp. skip. progress.
simplify tagGen. 
rewrite H2. simplify.
have : OTSMOracle.pkf{2} = (fun (i : int) => omap sk2pk (OTSMOracle.skf{2} i)).
smt.  
move => o. 
rewrite o.
apply (zup (fun (i : int) => omap sk2pk (OTSMOracle.skf{2} i)) 
            OTSMOracle.skf{2} OTSMOracle.slog{2} (binRec t{2})).
rewrite - o. smt.
qed.

                                  

op ubPRF : real.
axiom ubRule &m : forall (D <: Distinguisher), 
 `|Pr[ IND(PRFr_Wrapped, D).main() @ &m  : res ] 
     - Pr[ IND(RandomFunction, D).main() @ &m  : res ]| <= ubPRF.




section.

declare module A <: AdvBLT{-GameBLT, -Ts, -Ts2, -Ts3, -GameFR, -TagOracle, 
                          -BLTOracle, -BLTOracle2,  -BLTOracle', 
                          -RandomFunction, -PRFr_Wrapped, -OTSMOracle, 
                          -Ts, -BLTOracle, -GameBLT, -OTSOracle, -OWrapper, 
                          -Wrapper0, -WrapperP, -Wrapper', -Wrapper'', -GameOTSMP'', 
                          -GameOTSMP', -TagKeysEff}.



axiom qqq :  (forall (T <: Repo{-A}) (B <: BLTOracleT{-A}),
     islossless B.sign => islossless T.put => islossless A(T, B).forge).


lemma term : forall (O0 <: OTSMOracleT{-BinaryStuff}),
  islossless O0.sign =>
  islossless O0.getSigLog =>
  islossless O0.getMsgLog =>
  islossless O0.getPK => 
  islossless BinaryStuff(O0).tag.
proof. move => O l1 l2 l3 l4.
proc. inline*. if.
wp. skip. auto.
wp.
seq 3 : (ys <> []).
wp.  call (_:true). skip. auto.
wp. call l4. skip. auto. auto. smt.
call (_:true).
while true (size ys).
move => z. wp. 
call l1.
wp. skip. auto. smt.
skip.
smt.
wp. 
hoare.
call (_:true). 
skip. smt. auto.
qed.


local lemma d1 &m :  Pr[ GameBLT(A, Ts, BLTOracle(Ts, TagOracle), TagKeysEff).main() @ &m : res ] 
 <= Pr[ GameFR(BLT2FR(A), TagOracle, TagKeysEff).main() @ &m : res ].
proof. apply (blt2frUB (TagKeysEff) A (* qqq *) &m).
qed.


lemma ddd :   (forall (T <: TagOracleT{-BLT2FR(A)}),
     islossless T.tag => islossless BLT2FR(A, T).forge).
proof. move => T q. proc. inline*.
wp. call (qqq Ts3 (BLTOracle2(T))).
proc. 
inline*.
seq 2 : true.
wp. skip. auto.
wp. skip. auto. 
if. wp. call q.
skip. auto.
skip. auto.
wp. auto.
auto.
proc. inline*.
if.
wp.
skip. auto. skip. auto.
wp.  rnd. wp.  skip. smt.
qed.


local lemma d2 &m :  Pr[ GameBLT(A, Ts, BLTOracle(Ts, TagOracle), TagKeysEff).main() @ &m : res ] 
  <= Pr[ GameFR(BLT2FR(A), TagOracle, TagKeysPRF(PRFr_Wrapped)).main() @ &m : res ].
proof.
have : Pr[ GameFR(BLT2FR(A), TagOracle, TagKeysEff).main() @ &m : res ] 
  = Pr[ GameFR(BLT2FR(A), TagOracle, TagKeysPRF(PRFr_Wrapped)).main() @ &m : res ].
rewrite (leaPr (BLT2FR(A)) (* ddd *) &m). auto.
smt.
qed.


local module (Z : Distinguisher) (F:PRF_Oracles)  = {
    module Q = GameFR(BLT2FR(A), TagOracle, TagKeysPRF'(F))
    proc distinguish() = {
      var r;
      r <@ Q.main();
      return r;
    }
}.


local lemma qo1 : equiv [ IND(RandomFunction, Z).main 
  ~ GameFR(BLT2FR(A), TagOracle, TagKeysPRF(RandomFunction)).main 
  : ={glob TagOracle, glob A, glob Ts3} ==> ={res} ].
proc. inline*. 
wp. call (_: ={glob TagOracle, glob Ts3}). 
proc. sim.
proc. sim.
wp. rnd. wp. while (={i,skf,pkf,  glob RandomFunction}). wp. 
seq 1 1 : (={ skf, pkf,  i, x, glob RandomFunction}). wp. skip. smt.
if. progress. wp. rnd. skip. progress. skip. progress.
wp. skip. progress. 
qed.


local lemma qoPr1 &m : Pr [ IND(RandomFunction, Z).main() @ &m : res ] 
 = Pr[ GameFR(BLT2FR(A), TagOracle, TagKeysPRF(RandomFunction)).main() @ &m : res ].
proof. byequiv (_: ={glob TagOracle, glob A, glob Ts3} ==> _). conseq qo1. progress. auto. 
qed.


local lemma qo2 : equiv [ IND(PRFr_Wrapped, Z).main 
 ~ GameFR(BLT2FR(A), TagOracle, TagKeysPRF(PRFr_Wrapped)).main 
 : ={glob PRFr_Wrapped,  glob TagOracle, glob A, glob Ts3} ==> ={res} ].
proc. inline*. 
wp. call (_: ={glob TagOracle, glob Ts3, glob PRFr_Wrapped}). 
proc. sim. 
proc. sim.
wp. rnd. wp. while (={i,skf,pkf,  glob PRFr_Wrapped}). wp. 
seq 1 1 : (={ skf, pkf,  i,  glob PRFr_Wrapped}). wp. skip. smt. skip. progress.
wp. rnd. skip. progress. 
qed.


local lemma qoPr2 &m : Pr [ IND(PRFr_Wrapped, Z).main() @ &m : res ] 
 = Pr[ GameFR(BLT2FR(A), TagOracle, TagKeysPRF(PRFr_Wrapped)).main() @ &m : res ].
proof.  byequiv (_: ={glob PRFr_Wrapped, glob A, glob Ts3, glob TagOracle} ==> _). 
conseq qo2. progress. auto. auto.
qed.


local lemma qoubf &m : 
 `|Pr[ IND(PRFr_Wrapped, Z).main() @ &m : res ] - Pr[ IND(RandomFunction, Z).main() @ &m : res ]|
  <= ubPRF.
proof. apply (ubRule &m Z).
qed.


local lemma qoubf1 &m : Pr[ IND(PRFr_Wrapped, Z).main() @ &m : res ] 
 <= Pr[ IND(RandomFunction, Z).main() @ &m  : res ] + ubPRF.
proof. smt.
qed.


local lemma qoubf2 &m : 
 Pr[ GameFR(BLT2FR(A), TagOracle, TagKeysPRF(PRFr_Wrapped)).main() @ &m  : res ] 
 <= Pr[ IND(RandomFunction, Z).main() @ &m  : res ] + ubPRF.
proof. smt.
qed.


local lemma qoubf3 &m : 
 Pr[ GameFR(BLT2FR(A), TagOracle, TagKeysPRF(PRFr_Wrapped)).main() @ &m  : res ] 
 <= Pr[ GameFR(BLT2FR(A), TagOracle, TagKeysPRF(RandomFunction)).main() @ &m  : res ] + ubPRF.
proof. smt.
qed.


lemma zok : (forall (O0 <: OTSMOracleT{-WrapperFR(BinaryStuff, BLT2FR(A))}),
     islossless O0.sign =>
     islossless O0.getSigLog =>
     islossless O0.getMsgLog =>
     islossless O0.getPK =>
     islossless WrapperFR(BinaryStuff, BLT2FR(A), O0).forge). 
proof. move => O a1 a2 a3 a4.
proc. inline*. wp.
call (_:true). apply qqq. 
proc. inline*. sp. if. sp. if. wp. auto.
wp. call (_:true). while true (size ys).
move => z. wp. call (_:true). wp. auto. progress. smt.
wp. call (_:true). skip. progress. smt. skip. smt. proc.
auto. auto. smt.
qed.


local lemma fr2otsAndPRFUB &m : 
 Pr[ GameFR(BLT2FR(A), TagOracle, TagKeysPRF(PRFr_Wrapped)).main() @ &m  : res ] 
 <=  M%r * Pr[ GameOTS(OTSOracle, Wrapper0(WrapperFR(BinaryStuff,BLT2FR(A))), 
                                     K.SimpleKeyGen).main() @ &m : res ] + ubPRF.
proof. 
have : Pr[ GameFR(BLT2FR(A), TagOracle, TagKeysPRF(RandomFunction)).main() @ &m : res ]
 <= M%r * Pr[ GameOTS(OTSOracle, Wrapper0(WrapperFR(BinaryStuff,BLT2FR(A))), 
                                     K.SimpleKeyGen).main() @ &m : res ].
apply (fr2otsUB BinaryStuff (BLT2FR(A)) (* constr *) (* zok *) &m).
smt.
qed.


end section.
