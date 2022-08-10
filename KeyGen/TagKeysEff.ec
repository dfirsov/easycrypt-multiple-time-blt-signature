require import Int  Bool Real Distr List.

(* The main goal of the developments in this file is to establish the
equivalence of the outcomes of the FR game when played with the
efficient ("lazy") PRF based key generation and inefficient ("eager")
PRF based key generation (modules TagKeysEff and
TagKeysPRF(PRFr_Wrapped), respectively).

The final result is derived in lemma leaPr. *)

require MultipleTimeConstruction.
clone export MultipleTimeConstruction as MTO.


require KeyGen.
clone export KeyGen.KeyGen as K with type pkey <- pkey,
                                     type skey <- skey,
                                     op keyGen <- otsKey,
                                     op dR <- dR.


require OTS.
clone export OTS.OTS_Theory with type pkey <- pkey,
                                 type skey <- skey,
                                 type message <- message,
                                 type sig <- sig,
                                 op otsSig <- otsSig,
                                 op otsVer <- otsVer,
                                 op otsKey <- otsKey.

require OTSM.
clone export OTSM.OTSM_Theory with type pkey <- pkey,
                                   type skey <- skey,
                                   type message <- message,
                                   type sig <- sig,
                                   op M <- M,
                                   op otsKey <- otsKey,
                                   op dR <- dR,
                                   op otsSig <- otsSig,
                                   op otsVer <- otsVer
                                   proof NP.dK_ll by apply dR_ll
                                   proof NP.dR_ll by apply dR_ll
                                   proof *.



require BLT2FR.
clone export BLT2FR as C1 with type pkey          <- pkey,
                               type skey          <- Time -> skey option,
                               type tag           <- tag,
                               type message       <- message,
                               op tagGen          <- tagGen,
                               op tagVer          <- tagVer,
                               op tdistr          <- tdistr,
                               op EXP             <- EXP,
                               op dR              <- dR
                               proof tdAx by apply/tdAx.



require ConcretePRF.
clone export ConcretePRF as CPRF with type D  <- Time,
                                      type R  <- Time,
                                      type K  <- Time,
                                      op   dK <- dR,
                                      op dR <- dR,
                                      op F <- F
                                      proof dK_ll by apply dR_ll.




module TagKeysEff : KeyGenT = {
  var rs : int
  proc keyGen()  = {
    var pk, sk;
    rs <$ dR;
    pk <- fst (otsKey (F rs 1));
    sk <- fun x => if x <= 0 then None else Some (snd (otsKey (F rs x)));
    return (pk, sk);
  }
}.


module TagKeysPRF' (F : PRF_Oracles) : KeyGenT = {
  proc keyGen()  = {
     var pkf : (Time -> pkey option);
     var skf : (Time -> skey option);
     var i : Time;
     var pk : pkey;
     var sk : skey;
     var rs : int;
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
    return (oget (pkf 1), skf);
  }
}.


module TagKeysPRF (F : PRF_Hiding) : KeyGenT = {
  module K = TagKeysPRF'(F)
  proc keyGen()  = {
    var r;
    F.init();
    r <@ K.keyGen();
    return r;
  }
}.


lemma a1 n l : checkTagLog EXP (n :: l) => n < EXP.
proof. simplify. auto. qed.


lemma a2 n m l : !checkTagLog m l => !checkTagLog m (n :: l).
proof. simplify. move => h.
case (n < m). auto. auto. qed.


lemma a3 : forall t_R lt_R, checkTagLog t_R lt_R = false => exists q, q \in lt_R /\ t_R <= q.
proof. move => t_R lt_R h.
have : (t_R \in lt_R) \/ (exists q, q \in lt_R /\ t_R < q). 
apply (tpl t_R lt_R h).
move => h2.
elim h2. smt. smt.
qed.


lemma a3' : forall t_R (lt_R : Time list),  (exists (q : Time), q \in lt_R /\ t_R <= q) 
 => checkTagLog t_R lt_R = false.
proof.  move => t_R.
elim. smt.
move => x l h1 h2. simplify. smt.
qed.


lemma a4 n l : !checkTagLog EXP l => n <= EXP => !checkTagLog n l.
proof. smt.
qed.


section.
declare module A <: AdvFR{-TagOracle, -PRFr_Wrapped, -TagKeysEff}.


axiom tl : forall (T <: TagOracleT{-A}), islossless T.tag => islossless A(T).forge.
op eqOrLarger : int -> int list -> bool = fun x l => !(checkTagLog x l).


lemma z : equiv [ GameFR(A,TagOracle, TagKeysPRF(PRFr_Wrapped)).main 
  ~ GameFR(A, TagOracle, TagKeysEff).main : ={glob A} ==> ={res} ].
proof. proc.
inline*. wp.
call (_: eqOrLarger EXP  TagOracle.lt , 
   PRFr_Wrapped.k{1} = TagKeysEff.rs{2}
  /\ (forall i, 1 <= i /\ i <= M => (TagOracle.sk{1} i) = Some (snd (otsKey 
                                                           (F PRFr_Wrapped.k i)))){1}
  /\ (forall i, i <= 0  => (TagOracle.sk{1} i) = None){1}
  /\  (TagOracle.sk{2} = (fun x => if x <= 0 then None else Some (snd (otsKey 
                                                           (F TagKeysEff.rs x))))){2}
  /\ TagOracle.lt{1} = TagOracle.lt{2}   
   , eqOrLarger EXP TagOracle.lt{2} /\ eqOrLarger EXP  TagOracle.lt{1}).
apply tl.
proc. wp. skip. progress.
have : t{2} < EXP. smt.
move => pp.
have : (forall (j : int), j <= infoAhead t{2} => 
 TagOracle.sk{1} j  = (fun (x : int) => if x <= 0 then None else 
                           Some (otsKey (F TagKeysEff.rs{2} x)).`2) j).
case (t{2} <= 0). move => ass1. smt.
move => ass1.
simplify.
move => j jp.
case (j <= 0).  smt.
move => hp2.
have : 1 <= j. 
smt.
move => ho3.
have : 0 <= t{2}. smt.
smt.
move => gg.
smt (L_a5).
move => &1 ep. proc. wp. skip. smt.
move => &1. proc.  wp. skip. smt.
wp.
while {1} (1 <= i{1} 
 /\ i{1} <= M + 1
 /\ (forall j, 1 <= j /\ j < i => (skf j) = Some (snd (otsKey (F PRFr_Wrapped.k j)))){1} 
 /\ (forall i, i <= 0  => (skf{1} i) = None){1}
 /\ (forall j, 1 <= j /\ j < i => (pkf j) = Some (fst (otsKey (F PRFr_Wrapped.k j)))){1}) 
    ((M+1) - i{1}). 
move => _ z.
wp. skip. progress;smt. 
wp. rnd.
skip.
progress;smt.
qed.


lemma leaPr &m : Pr[ GameFR(A, TagOracle, TagKeysPRF(PRFr_Wrapped)).main() @ &m : res ] 
  = Pr[ GameFR(A, TagOracle, TagKeysEff).main() @ &m : res ].
proof. byequiv. conseq z; auto. auto. auto.
qed.

end section.
