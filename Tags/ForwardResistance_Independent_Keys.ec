require import Int Bool Distr List Real SmtMap BasicProps KeyGen.

(* The main goal of this development is to prove that the probability
of breaking the multiple-time forward-resistance for the independently
generated keypairs is upper bounded by the expiration time times the
probability of breaking the unforgeability of the underlying one-time
signatures. 

The main result is derived in lemma fr2otsUB.
*)

require OTSM2OTS.
clone export OTSM2OTS as O.
                            
op splitf ['a] (p : 'a -> bool)
    (xs : 'a list) : 'a = 
    with xs = "[]" => witness
    with xs = (::) y ys => if all (fun x => !p x) ys 
                           then y else splitf p ys.

op parseTagList : (int -> pkey option) -> (int * message * sig) list -> int * message * sig
 = fun pkf l => splitf (fun (e : int * message * sig) => otsVer (pkf e.`1) e.`2 e.`3) l.

op parseTag : (int -> pkey option) -> (int * tag option) ->  int * message * sig 
 = fun pkf q =>  parseTagList pkf (tag2list q).


lemma slw ['a] (p : 'a -> bool) : 
 forall (xs : 'a list) q1 e q2, xs = q1 ++ e :: q2 
 /\ (forall e, e \in q2 => !p e) 
 /\ p e => splitf p xs = e.
proof. elim. smt.
move => x l h q1 e q2 h'.
simplify.
case (q1 = []).
move => g.
case (all (fun (x0 : 'a) => ! p x0) l).
move => h2. smt. smt.
move => w.
have : exists y ys, q1 = y :: ys. smt (oa2).
elim. move => y ys w2.
have : x = y. smt.
move => w3.
case (all (fun (x0 : 'a) => ! p x0) l).
timeout 20. smt.
move => w4.
apply (h ys e q2). smt.
qed.

 
lemma pl3 pkf q1 (e : int * message * sig) (q2 : (int * message * sig) list) : 
 (forall e, e \in q2 => !otsVer ((pkf e.`1)) e.`2 e.`3) 
 => otsVer (pkf e.`1) e.`2 e.`3  = true 
 => parseTagList pkf (q1 ++ e :: q2) = e.
proof. move => h z. 
apply (slw (fun (e : int * message * sig) => otsVer (pkf e.`1) e.`2 e.`3) (q1 ++ e :: q2)  
        q1 e q2).
smt.
qed.


section.


module type TagOracleWrapperT(O : OTSMOracleT) = {
  proc init(pk : pkey, skf : int -> skey option)   : unit
  proc pks (pkf : int -> pkey option)   : unit {}
  proc tag(t : int)  : tag option {O.sign, O.getSigLog, O.getMsgLog, O.getPK}
  proc getTagLog() : int list {}
}.


declare module O <: TagOracleWrapperT{-OTSMOracle, -TagOracle, -OTSOracle, -RandomFunction, -OWrapper, -Wrapper0, -WrapperP,  -Wrapper'', -GameOTSMP', -GameOTSMP'', -Wrapper'}.
declare module A <: AdvFR{-TagOracle, -OTSMOracle, -RandomFunction, -O, -OTSOracle, -OWrapper, -Wrapper0, -GameOTSMP', -GameOTSMP'', -RandomFunction, -WrapperP, -Wrapper'', -GameOTSMP', -GameOTSMP'', -Wrapper'}.

axiom toTagConv : equiv [ TagOracle.tag ~ O(OTSMOracle).tag : 
 TagOracle.sk{1} = OTSMOracle.skf{2} 
 /\ (forall i, OTSMOracle.pkf{2} i = (omap sk2pk (OTSMOracle.skf{2} i))) 
 /\ ={arg}
 /\ (forall (i : int) (m : message), OTSMOracle.log.[i]{2} = Some m 
        => exists j, i <= j /\ j \in TagOracle.lt{1})
 /\ (forall i m, OTSMOracle.log.[i] = Some m => m = msg OTSMOracle.pkf i){2}
 /\ (forall i,  OTSMOracle.used{2}.[i] = Some ()  => OTSMOracle.slog{2}.[i] <> None)
 /\ (forall i s, OTSMOracle.slog.[i] = Some s => 
       s = otsSigMany OTSMOracle.skf i (msg OTSMOracle.pkf i)){2}
  ==> ={res} 
 /\  (forall (i : int) (m : message), OTSMOracle.log.[i]{2} = Some m 
       => exists j, i <= j /\ j \in TagOracle.lt{1})
 /\ (forall i m, OTSMOracle.log.[i] = Some m => m = msg OTSMOracle.pkf i){2}
 /\ (forall i s, OTSMOracle.slog.[i] = Some s 
       => s = otsSigMany OTSMOracle.skf i (msg OTSMOracle.pkf i)){2}
 /\ (forall i,  OTSMOracle.used{2}.[i] = Some () => OTSMOracle.slog{2}.[i] <> None)
 ].


lemma pl10 pk i tg : tagVer pk i tg = true => tag2list (i,tg) <> [].
proof. smt (L_pl4). qed.


lemma pl2 pkf (itg : int * tag option) : pkf 1 <> None 
 => tagVer (oget (pkf 1)) itg.`1 itg.`2 = true 
 => exists q1 e q2, tag2list itg = (q1 ++ e :: q2) 
    /\ (forall e, e \in q2 => !otsVer (pkf e.`1) e.`2 e.`3)
    /\ otsVer (pkf e.`1) e.`2 e.`3.
proof. move => h1 h2.
have : has (fun (e : int * message * sig) => otsVer (pkf e.`1) e.`2 e.`3) (tag2list itg) .
case (tag2list itg = []). smt (pl10).
move => j1.
have : exists pkz, pkf 1 = Some pkz. smt (oa1).
elim. move => pkz j3.
have : exists e q, tag2list itg = (e::q). smt (oa2).
elim. move => e q j2.
have : otsVer (Some pkz) e.`2 e.`3 = true. smt.
move => j4.
have : exists e, (e \in tag2list itg) /\ otsVer (pkf e.`1) e.`2 e.`3. 
exists e. rewrite j2. progress. smt (L_pl11).
move => qqq. smt.
move => hl.
apply (slz (fun (e : int * message * sig) => otsVer (pkf e.`1) e.`2 e.`3) (tag2list itg) hl).
qed.


lemma pl8 pkf i tg x y z  : pkf 1 <> None =>
  tagVer (oget (pkf 1)) i tg = true
 => parseTag pkf (i, tg) = (x,y,z) => x <= i
    /\ 0 < x 
    /\ otsVer (pkf x) y z = true.
proof. move => h1 h2 h3.
have : exists q1 e q2, tag2list (i,tg) = (q1 ++ e :: q2) 
  /\ (forall e, e \in q2 => !otsVer (pkf e.`1) e.`2 e.`3)
  /\ otsVer (pkf e.`1) e.`2 e.`3. smt (pl2).
elim. move => q1 e q2 hs.
have : e \in tag2list (i,tg). smt.
move => g1.
have : e.`1 <= i /\ 0 < e.`1. smt.
have : parseTag pkf (i, tg) = e. smt.
move => h4.
have : (x, y, z) = e. smt.
move => h5.
smt.
qed.


lemma pl1 pkf l i m s : otsVer (pkf i) m s  => parseTagList pkf (l ++ (i,m,s) :: []) = (i,m,s).
proof. smt (pl3). qed.



module WrapperFR(O : TagOracleWrapperT, A : AdvFR, OTSO : OTSMOracleT) = {
  module B = O(OTSO)
  module A = A(B)
  
  proc forge(pk : int -> pkey option) : int * message * sig = {
    var r;
    r <@ A.forge(oget (pk 1));
    return (parseTag pk r);
  }
}.




lemma main' : equiv [ A(TagOracle).forge ~ WrapperFR(O, A, OTSMOracle).A.forge : 
 TagOracle.sk{1} = OTSMOracle.skf{2} 
 /\ ={arg} /\ ={glob A} 
 /\ TagOracle.lt{1} = []
 /\ OTSMOracle.log{2} = empty
 /\ (forall i, OTSMOracle.pkf{2} i = (omap sk2pk (OTSMOracle.skf{2} i)))
 /\ (forall i, OTSMOracle.used{2}.[i] = Some ()  => OTSMOracle.slog{2}.[i] <> None)
 /\ (forall i s, OTSMOracle.slog.[i] = Some s 
      => s = otsSigMany OTSMOracle.skf i (msg OTSMOracle.pkf i)){2} 
  ==> ={res} 
 /\ (forall (i : int) (m : message), OTSMOracle.log.[i]{2} = Some m 
        => exists j, i <= j /\ j \in TagOracle.lt{1})
 /\ (forall i m, OTSMOracle.log.[i] = Some m => m = msg OTSMOracle.pkf i){2}
 /\ (forall i, OTSMOracle.pkf{2} i = (omap sk2pk (OTSMOracle.skf{2} i))) ].
proof. proc*.
call (_: TagOracle.sk{1} = OTSMOracle.skf{2} 
  /\  (forall (i : int) (m : message), OTSMOracle.log.[i]{2} = 
         Some m => exists j, i <= j /\ j \in TagOracle.lt{1})
  /\ (forall i m, OTSMOracle.log.[i] = Some m => m = msg OTSMOracle.pkf i){2}
  /\ (forall i, OTSMOracle.pkf{2} i = (omap sk2pk (OTSMOracle.skf{2} i)))
  /\ (forall i,  OTSMOracle.used{2}.[i] = Some ()  => OTSMOracle.slog{2}.[i] <> None)
  /\ (forall i s, OTSMOracle.slog.[i] = Some s 
       => s = otsSigMany OTSMOracle.skf i (msg OTSMOracle.pkf i)){2} ).
conseq toTagConv. auto. progress.  
skip.
progress. smt. smt.
qed.


lemma main''  : equiv [ GameFR(A, TagOracle, TagKeysPRF(RandomFunction)).main ~ 
 GameOTSM(OTSMOracle, WrapperFR(O,A), KeyGenOTSM(RandomFunction)).main : 
 ={glob A, glob RandomFunction} ==> res{1} => res{2} ].
proof. 
proc. inline*. wp.
call main'.
wp. 
while (={i,pkf,skf, glob RandomFunction, glob A} 
 /\ (forall i pk sk, pkf{1} i = Some pk => skf{1} i = Some sk 
      => exists rs, (pk, sk) = otsKey rs) 
 /\ (forall j, j < i{1} /\ 0 < j => pkf{1} j <> None) 
 /\ (forall i, pkf{2} i = (omap sk2pk (skf{2} i)))).
wp.
seq 1 1 : (={x,i, pkf, skf, glob RandomFunction, glob A} 
  /\ i{1} < M + 1 
  /\ i{2} < M + 1 
  /\ (forall i pk sk, pkf{1} i = Some pk => skf{1} i = Some sk 
       => exists rs, (pk, sk) = otsKey rs)
  /\ (forall j, j < i{1} /\ 0 < j => pkf{1} j <> None) 
  /\ (forall i, pkf{2} i = (omap sk2pk (skf{2} i)))).
wp. skip. auto.
if. auto. wp. rnd. skip.
progress. timeout 10. smt. smt. smt.
skip. progress. smt. smt. smt. wp. skip. 
progress. smt. smt. smt.
have : (parseTag pkf_R result_R).`1 <= result_R.`1 
 /\ 0 < (parseTag pkf_R result_R).`1 
 /\ otsVer (pkf_R (parseTag pkf_R result_R).`1) 
           (parseTag pkf_R result_R).`2 
           (parseTag pkf_R result_R).`3 = true.
smt (pl8 MEXP).
smt.
have : (parseTag pkf_R result_R).`1 <= result_R.`1 
  /\ 0 < (parseTag pkf_R result_R).`1 
  /\ otsVer (pkf_R (parseTag pkf_R result_R).`1) 
            (parseTag pkf_R result_R).`2 
            (parseTag pkf_R result_R).`3 = true.
smt (pl8 MEXP).
smt.
have : (parseTag pkf_R result_R).`1 <= result_R.`1 
 /\ 0 < (parseTag pkf_R result_R).`1 /\ 
     otsVer (pkf_R (parseTag pkf_R result_R).`1) 
            (parseTag pkf_R result_R).`2 
            (parseTag pkf_R result_R).`3 = true.
smt (pl8 MEXP).
smt.
have : exists q1 e q2, tag2list result_R = (q1 ++ e :: q2) 
  /\ (forall e, e \in q2 => !otsVer ((pkf_R e.`1)) e.`2 e.`3)
  /\ otsVer ((pkf_R e.`1)) e.`2 e.`3. 
apply (pl2 pkf_R result_R). smt. smt.
elim.
move => q1 e q2 h0.
elim h0. move => h1 h0.
elim h0. move => h2 h3.
case (q2 = []).
(* case 1 *)
move => h4.
have : exists q m s, tag2list result_R = q ++ (result_R.`1,m,s) :: []. 
apply (L_pl4 (oget (pkf_R 1)) result_R). smt.
elim. move => q1' m s h5.
have : e = (result_R.`1, m, s). smt.
move => h6.
simplify parseTag.
rewrite h1.
rewrite h4.
rewrite h6.
have : parseTagList pkf_R (q1 ++ [(result_R.`1, m, s)]) = (result_R.`1, m, s). smt.
move => h7. rewrite h7.
have :  pkf_R result_R.`1 <> None. smt.
move => g1.
have : exists pkz, pkf_R result_R.`1 = Some pkz. 
smt (oa1).
elim.
move => pkz h8.
case (log_R.[(result_R.`1, m, s).`1] = None). smt.
move => zkp. 
have : exists mz,  log_R.[result_R.`1] = Some mz. smt (oa1).
elim. move => mz.
move => zkp2.
have : exists (j : int), result_R.`1 <= j /\ (j \in lt_L). smt.
move => qq1.
have : !checkTagLog result_R.`1 lt_L. smt (a3').
move => qq2.
smt.
(* case 2 *)
move => h4.
have : exists e' es', q2 = e'::es'. smt (oa2).
elim. move => e' es' h5.
simplify parseTag.
rewrite h1.
rewrite h5.
have : otsVer (pkf_R e'.`1) e'.`2 e'.`3 = false. smt.
move => h6.
have : otsVer ((msg2key e.`2 e'.`1)) e'.`2 e'.`3 = true. 
smt (L_pl7).
move => h9.
have : (msg2key e.`2 e'.`1)  <> None. smt (L_pl0).
move => h7.
have : exists pke, (msg2key e.`2 e'.`1) = Some pke. smt (oa1).
elim. move => pke pkeq.
have : (parseTagList pkf_R (q1 ++ e :: e' :: es')) = e.
smt (pl3). 
move => h71.
have : msg2key e.`2 e'.`1 <> pkf_R e'.`1. smt.
move => h8.
rewrite h71.
case (Some e.`2 = log_R.[e.`1]).
move => h10.
have : e.`2 = msg pkf_R e.`1. smt.
move => h12.
smt (L_pl5).
auto.
qed.


lemma main &m : Pr[ GameFR(A, TagOracle, TagKeysPRF(RandomFunction)).main() @ &m : res ] 
 <= Pr[ GameOTSM(OTSMOracle, WrapperFR(O,A), KeyGenOTSM(RandomFunction)).main() @ &m 
        : res ].
byequiv (_: ={glob A, glob RandomFunction, glob TagOracle} ==> _). 
conseq main''. auto. auto. auto.
qed.


(* if oracle procedures terminate then adversary must also be terminating *)
axiom hzc : (forall (O0 <: OTSMOracleT{-WrapperFR(O, A)}),
     islossless O0.sign =>
     islossless O0.getSigLog =>
     islossless O0.getMsgLog =>
     islossless O0.getPK => islossless WrapperFR(O, A, O0).forge).

lemma fr2otsUB &m :
 Pr[ GameFR(A, TagOracle, TagKeysPRF(RandomFunction)).main() @ &m  : res ]
 <= M%r * Pr[ GameOTS(OTSOracle,
               Wrapper0(WrapperFR(O,A)), K.SimpleKeyGen).main() @ &m : res ].
proof.
have : Pr[ GameOTSM(OTSMOracle, WrapperFR(O,A),
            KeyGenOTSM(RandomFunction)).main() @ &m : res ]
 <= M%r * Pr[ GameOTS(OTSOracle, Wrapper0(WrapperFR(O,A)),
                                     K.SimpleKeyGen).main() @ &m : res ].
apply (otsm2otsUB (WrapperFR(O,A)) (* hzc *) &m ).
smt.
qed.

end section.

