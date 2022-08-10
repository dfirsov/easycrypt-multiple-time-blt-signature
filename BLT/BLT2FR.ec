require import Int Bool SmtMap Distr List Real AllCore.

(* The development in this file performs a serious of reductions to
establish the lemma "blt2frUB" which proves that the probability of
breaking the existential unforgeability of the multiple-time BLT is
upper bounded by the probability of breaking the forward-resistance of
the underlying tag system. *)

type Time = int.
type pkey, skey, tag, message.
op tdistr : Time distr.
op tagGen : skey -> Time -> tag option.
op tagVer : pkey -> Time -> tag option -> bool.
op EXP : Time.
op dR : int distr.


require BLT.

clone export BLT.BLT_Scheme_Theory with type pkey     <- pkey,
                                        type skey     <- skey,
                                        type tag      <- tag,
                                        type message  <- message,
                                        op tagGen     <- tagGen,
                                        op tagVer     <- tagVer,
                                        op tdistr     <- tdistr,
                                        op EXP        <- EXP,
                                        op dR         <- dR.

axiom tdAx i : i \in tdistr => 0 < i.


module Ts2 : Repo = {
  var r : (Time, message * tag option) fmap  
  var f : bool
  var i : Time              
  var t : Time              
  var pk : pkey
  proc init() = {
    i <$ tdistr;            
    t <-  i;
    r <-  empty<:Time, message * tag option>;
    f <- false;
  }  
  proc clock() = {
    return t;
  }  
  proc put(d : message * tag option) = {
    t <- t + 1;
    r <- r.[t <- d];
    f <- f \/ (t <= EXP /\ tagVer pk t (snd d));
    return t;
  }
  proc oput(d : message * tag option) = {
    t <- t + 1;
    r <- r.[t <- d];
    return t;
  }
  proc check(i : Time, m : message * tag option) : bool = {
    return r.[i] = Some m;
  }
}.


module Ts3 : Repo = {
  var r : (Time, message * tag option) fmap  
  var t : Time               
  var f : bool
  var i : Time               
  var pk : pkey
  proc init() = {
    i <$ tdistr;             
    t <-  i;
    r <-  empty<:Time, message * tag option>;
    f <- false; 
    pk <- witness;
  }  
  proc clock() = {
    return t;
  }      
  proc put(d : message * tag option) = {
    if(!f){
    t <- t + 1;
    r <- r.[t <- d];
      f <- f \/ (t <= EXP /\ tagVer pk t (snd d));
    }
    return t;
  }
  proc oput(d : message * tag option) = {
    t <- t + 1;
    r <- r.[t <- d];
    return t;
  }
  proc check(i : Time, m : message * tag option) : bool = {
    return r.[i] = Some m;
  }
}.


module BLTOracle'  : BLTOracleT = {
  module T = TagOracle
  module R = Ts2
  var l : message list
  proc init(pk : pkey, sk : skey) = {
    R.init();
    R.pk <- pk;
    T.init(pk, sk);
    l <- [];
  }  
  proc sign(m : message) = { 
     var t, tg;
     t <@ R.clock();
     tg <@ T.tag(t+1); 
     R.oput((m,tg));
     l <- m :: l;
     return (t, tg);
  }
  proc fresh(m : message) : bool = {
     return !(m \in l);
  }  
}.


module BLTOracle2 (T : TagOracleT) : BLTOracleT = {
  var l : message list
  proc init(pk:pkey, sk:skey) = {
    Ts3.init();
    Ts3.pk <- pk;
    T.init(pk, sk);
    l <- [];
  }  
  proc sign(m : message) = { 
     var t, tg;
     t <@ Ts3.clock();
     tg <- witness;
     if(!Ts3.f){
      tg <@ T.tag(t+1); 
      Ts3.oput(m,tg);
      l <- m :: l;
     }
     return (t, tg);
  }
  proc fresh(m : message) : bool = {
     return !(m \in l);
  }  
}.


lemma tpl : forall t_R lt_R, checkTagLog t_R lt_R = false 
  => (t_R \in lt_R) \/ (exists q, q \in lt_R /\ t_R < q).
proof. move => t_R. elim.
auto. move => x l z o. 
case (checkTagLog t_R l = true). move => zz.
have : checkTagLog t_R (x :: l) = x < t_R. simplify delta. rewrite zz //= => q. 
move => u1. rewrite o in u1.
have : (t_R <= x). smt. case (t_R = x). smt.
smt. move => ll. smt.
qed.


section.
declare module K <: KeyGenT{-GameBLT, -Ts, -Ts2, -Ts3,  -TagOracle, -BLTOracle2, -BLTOracle, -BLTOracle'}.
declare module A <: AdvBLT{-GameBLT, -Ts, -Ts2,  -Ts3, -TagOracle, -BLTOracle2, -BLTOracle, -BLTOracle', -K}.
axiom fl : forall (T <: Repo{-A}) (B <: BLTOracleT{-A}),
  islossless B.sign => islossless T.put => islossless A(T, B).forge.


local lemma nosmt ee : equiv [ GameBLT(A, Ts, BLTOracle(Ts, TagOracle), K).main 
 ~ GameBLT(A, Ts2, BLTOracle', K).main : ={glob A, glob BLTOracle, glob K} 
 ==> ={res} ].
proof. proc. inline*. wp.
call (_:    Ts.t{1} = Ts2.t{2} /\ BLTOracle.l{1} = BLTOracle'.l{2} 
         /\ Ts.r{1} = Ts2.r{2} /\ ={glob TagOracle}).
proc. inline*. wp. skip. progress.
proc. inline*. wp. skip. progress. 
wp. rnd. wp. call (_: true). skip. progress. 
qed.


local lemma nosmt eePr &m : Pr[ GameBLT(A, Ts, BLTOracle(Ts, TagOracle), K).main() @ &m : res ] 
 = Pr[ GameBLT(A, Ts2, BLTOracle', K).main() @ &m : res ].
proof. byequiv (_ : ={glob A, glob BLTOracle, glob K} ==> _). conseq ee;auto. auto. auto.
qed.


local lemma nosmt oo : equiv [ GameBLT(A, Ts2, BLTOracle', K).main 
 ~ GameBLT(A, Ts2, BLTOracle', K).main :
  ={glob A, glob BLTOracle', glob TagOracle, glob K} 
 ==> res{1} = (res{2} /\ Ts2.f{2} 
  /\ GameBLT.i{2} <= EXP) ].
proof. proc. inline*. wp.
call (_:  ={glob Ts2,  glob TagOracle, glob BLTOracle', glob K}  
   /\ (forall i, i \in TagOracle.lt => i <= Ts2.t){1}
   /\ (Ts2.f => exists i d, Ts2.r.[i] = Some d /\ i <= Ts2.t => !(i \in TagOracle.lt)){1}
   /\ (!Ts2.f => forall i d, Ts2.r.[i] = Some d => i <= EXP 
        /\ tagVer Ts2.pk i (snd d)  => (fst d) \in BLTOracle'.l){1}
   ).
proc. inline*. wp. skip. progress;smt.
proc. wp. skip. progress;smt.
wp. rnd. wp. call (_:true).  skip.
progress;smt.
qed.


local lemma nosmt ooPr &m : Pr[ GameBLT(A, Ts2, BLTOracle', K).main() @ &m : res ] 
  = Pr[ GameBLT(A, Ts2, BLTOracle', K).main() @ &m : res /\ Ts2.f /\ GameBLT.i <= EXP ].
proof. byequiv (_ : ={glob A, glob BLTOracle', glob TagOracle, glob K} ==> _). 
conseq oo;auto. auto. auto. 
qed.


local lemma nosmt qq : equiv [ GameBLT(A, Ts2, BLTOracle', K).main 
  ~ GameBLT(A, Ts3, BLTOracle2(TagOracle), K).main : ={glob A, glob K}
    ==> res{1} /\ Ts2.f{1} 
     /\ GameBLT.i{1} <= EXP  => Ts3.f{2} 
   ].
proof. symmetry. 
proc. inline*. wp.
call (_: Ts2.f, Ts2.f{2} = Ts3.f{1} /\ Ts2.t{2} = Ts3.t{1} 
  /\ Ts2.pk{2} = Ts3.pk{1} 
  /\ ={glob TagOracle, glob K}, Ts2.f{2} = Ts3.f{1}).
apply fl.
proc.
inline*. wp. skip. progress. 
move => &1 h.
proc. inline*. wp. skip. progress.
move => &1. proc. inline*. wp. skip. progress. 
proc. inline*. wp. skip. progress. 
move => &1 h. proc. wp. skip. progress. 
move => &1. proc. wp. skip. progress;smt.
wp. rnd. wp. call(_:true). skip. progress.
smt.    
qed.


local lemma qqPr &m : 
 Pr[ GameBLT(A, Ts2, BLTOracle', K).main() @ &m : res /\ Ts2.f /\ GameBLT.i <= EXP ] 
 <= Pr[ GameBLT(A, Ts3, BLTOracle2(TagOracle), K).main() @ &m : Ts3.f ].
proof. byequiv (_ : ={glob A, glob BLTOracle, glob TagOracle, glob K} ==> _).
conseq qq. progress. auto. auto.
qed.


local lemma nosmt zz : equiv [ GameBLT(A, Ts3, BLTOracle2(TagOracle), K).main 
 ~ GameBLT(A, Ts3, BLTOracle2(TagOracle), K).main : 
 ={glob A, glob K} 
 ==> (Ts3.f{1} = Ts3.f{2}) 
 /\  (forall i, i \in Ts3.r => 0 < i){2}
 /\  (forall i, i \in TagOracle.lt => i <= Ts3.t){2}
 /\  (Ts3.f => exists d, Ts3.r.[Ts3.t] = Some d 
      /\ !(Ts3.t \in TagOracle.lt) /\ tagVer Ts3.pk Ts3.t (snd d) /\ Ts3.t <= EXP){2}
  ].
proof. proc. inline*. wp.
call (_:  ={glob Ts3, glob TagOracle, glob BLTOracle2, glob K} 
  /\ (forall i, i \in TagOracle.lt => i <= Ts3.t){1}
  /\ (0 < Ts3.t){1}
  /\  (forall i, i \in Ts3.r => 0 < i){1}
  /\ (!Ts3.f => forall i d, Ts3.r.[i] = Some d => i <= EXP 
        /\ tagVer Ts3.pk i (snd d) => fst d \in BLTOracle2.l ){1}
  /\  (Ts3.f => exists d, Ts3.r.[Ts3.t] = Some d 
        /\ !(Ts3.t \in TagOracle.lt) /\ tagVer Ts3.pk Ts3.t (snd d) /\ Ts3.t <= EXP){2}
   ).
proc. inline*. wp. skip. progress;smt.
proc. inline*. wp. skip. progress;smt.
wp. rnd. wp. call (_:true). skip. progress;smt.
qed.


local lemma nosmt zzPr &m : Pr[ GameBLT(A, Ts3, BLTOracle2(TagOracle), K).main() @ &m : Ts3.f ] 
    = Pr[ GameBLT(A, Ts3, BLTOracle2(TagOracle), K).main() @ &m : Ts3.f
   /\ (forall i, i \in Ts3.r => 0 < i)
   /\ (forall i, i \in TagOracle.lt => i <= Ts3.t)
   /\ (exists d, Ts3.r.[Ts3.t] = Some d /\ !(Ts3.t \in TagOracle.lt) 
          /\ tagVer Ts3.pk Ts3.t (snd d) /\ Ts3.t <= EXP) ].
proof. byequiv (_: ={glob A, glob BLTOracle, glob TagOracle, glob K} ==> _). 
conseq zz. progress. auto. auto. progress. smt. auto. auto.
qed.


module BLT2FR(A : AdvBLT, T : TagOracleT)  = {
  module A = A(Ts3, BLTOracle2(T))
  proc forge(pk:pkey) = {
    var r;
    Ts3.init();
    Ts3.pk <- pk;
    A.forge(pk);
    r <- oget (Ts3.r.[Ts3.t]);
    return (Ts3.t, snd r);
  }  
}.


local lemma nosmt ll : equiv [ GameBLT(A, Ts3, BLTOracle2(TagOracle), K).main 
  ~ GameFR(BLT2FR(A), TagOracle,K).main : 
 ={glob A, glob K}
 ==>  Ts3.f{1}
 /\ (forall i, i \in Ts3.r => 0 < i){1}
 /\  (forall i, i \in TagOracle.lt => i <= Ts3.t){1}
 /\  (Ts3.f => exists d, Ts3.r.[Ts3.t] = Some d 
 /\ !(Ts3.t \in TagOracle.lt) 
 /\ tagVer Ts3.pk Ts3.t (snd d) 
 /\ Ts3.t <= EXP){1} => res{2}
   ].
proof.
proc. inline*. wp.
call (_: ={glob Ts3, glob TagOracle}).
proc. inline*. wp. skip.  progress.
proc. inline*. wp. skip.  progress.
wp. rnd. wp. call (_:true). skip. progress;smt.
qed.


local lemma nosmt llPr &m : 
 Pr[ GameBLT(A, Ts3, BLTOracle2(TagOracle), K).main() @ &m :
     Ts3.f
  /\  (forall i, i \in Ts3.r => 0 < i)
  /\  (forall i, i \in TagOracle.lt => i <= Ts3.t)
  /\  (exists d, Ts3.r.[Ts3.t] = Some d 
       /\ !(Ts3.t \in TagOracle.lt) 
       /\ tagVer Ts3.pk Ts3.t (snd d) /\ Ts3.t <= EXP) ] 
 <= Pr[ GameFR(BLT2FR(A), TagOracle, K).main() @ &m : res ].
byequiv (_: ={glob A, glob BLTOracle, glob TagOracle, glob K} ==> _). 
conseq ll. progress. auto. auto. progress. smt. auto. auto.
qed.


lemma nosmt blt2frUB &m : Pr [ GameBLT(A, Ts, BLTOracle(Ts, TagOracle), K).main() @ &m : res ]
  <= Pr[ GameFR(BLT2FR(A), TagOracle, K).main() @ &m : res ].
proof. rewrite (eePr &m). rewrite (ooPr &m).
have : Pr[GameBLT(A, Ts2, BLTOracle', K).main() @ &m : res /\ Ts2.f /\  GameBLT.i <= EXP] 
<= Pr[ GameBLT(A, Ts3, BLTOracle2(TagOracle), K).main() @ &m : Ts3.f ].
apply (qqPr &m).
move => h.
have : Pr[ GameBLT(A, Ts3, BLTOracle2(TagOracle), K).main() @ &m : Ts3.f ] 
 = Pr[ GameBLT(A, Ts3, BLTOracle2(TagOracle), K).main() @ &m : Ts3.f 
 /\  (forall i, i \in Ts3.r => 0 < i)
 /\  (forall i, i \in TagOracle.lt => i <= Ts3.t)
 /\  (exists d, Ts3.r.[Ts3.t] = Some d /\ !(Ts3.t \in TagOracle.lt) 
         /\ tagVer Ts3.pk Ts3.t (snd d) /\ Ts3.t <= EXP) ].
apply (zzPr &m).
move => h2.
have : forall (a b c : real), a <= b => b <= c => a <= c. smt.
move => h3.
apply (h3 (Pr[GameBLT(A, Ts2, BLTOracle', K).main() @ &m : res /\ Ts2.f /\ GameBLT.i <= EXP]) 
          (Pr[GameBLT(A, Ts3, BLTOracle2(TagOracle), K).main() @ &m :
                     Ts3.f
                 /\  (forall i, i \in Ts3.r => 0 < i)
                 /\  (forall i, i \in TagOracle.lt => i <= Ts3.t) 
                 /\  exists (d : message * tag option),
                       Ts3.r.[Ts3.t] = Some d 
                      /\ ! (Ts3.t \in TagOracle.lt) 
                      /\ tagVer Ts3.pk Ts3.t (snd d) 
                      /\ Ts3.t <= EXP]) 
   (Pr[GameFR(BLT2FR(A), TagOracle, K).main() @ &m : res])).
smt.
apply (llPr &m).
qed.


end section.
