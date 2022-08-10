require import Distr DInterval AllCore List BasicProps SmtMap.

(* The main goal of this development is to implement a multiple-time
forward-resistant tag system based on authentication paths.

Here, the main results are:
  # tagGen - tag generation function
  # tagVer - tag verification function
  # multTagsCorrect - proof that tag verification agrees with tag generation


*)


(* Parameters: types *)
type Time = int.
type pkey, skey,  sig.
type message = int * (pkey option) * (pkey option).
type tag = (int * message * sig) list.

(* Parameters: one-time signature scheme *)
op otsSig : skey -> message -> sig.
op otsVer : pkey option -> message -> sig -> bool.
op otsKey : int -> pkey * skey.
op sk2pk : skey -> pkey.
axiom otsCorrect rs pk sk m : (pk, sk) = otsKey rs =>  otsVer (Some pk) m (otsSig sk m) = true.
axiom sk2pkLaw rs pk sk : (pk, sk) = otsKey rs =>  pk = sk2pk sk.
axiom L_pl0: forall (m : message) (s : sig), otsVer None m s = false.

(* Parameters: positive expiration date *)
op EXP : Time.
axiom Npos : 1 <= EXP.

op dR : int distr = dinter 1 (2^512).
op tdistr : Time distr = dinter 1 EXP.


(* CONSTRUCTION: Tag Generation *)
op msg : (Time -> pkey option) -> Time -> message = fun pkf i => (i, pkf (2*i), pkf (2*i + 1)).


op tagGen' (pkf : Time -> pkey option)  (skf : Time -> skey option) (xs : Time list) : tag
 = foldr (fun n r => 
        (n, (msg pkf n), otsSig (oget (skf n)) (msg pkf n)) :: r) [] xs.


op tagGen : (Time -> skey option) -> Time -> tag option
 = fun skf i => if i <= 0 then None else  Some 
    (tagGen' (fun i => omap sk2pk (skf i)) skf (binRec i)).

(* CONSTRUCTION: Tag Verification *)
op tag2list : (Time * tag option) -> (Time * message * sig) list 
 = fun (x : int * tag option) => if x.`2 = None then [] else oget x.`2.


op msg2key : message -> Time -> pkey option 
 = fun (m: message) i => if i = 2 * m.`1  then m.`2 else if i = 2 * m.`1 + 1 then m.`3 else None.


op checkPair : (Time * message * sig) -> (Time * message * sig) -> bool 
 = fun (x x' : Time * message * sig) => otsVer (msg2key x'.`2 x.`1) x.`2 x.`3 .


op checkChain (tl : (Time * message * sig) list) : bool = 
  with tl = [] => true
  with tl = x :: xs => 
   (if xs = [] then true else checkPair (head witness xs) x) /\ checkChain xs.


op tagVerH (pk : pkey) (i : Time) (tl : (Time * message * sig) list) : bool = 
  with tl = [] => false
  with tl = x :: xs => x.`1 = 1 
                    /\ (last x tl).`1 = i 
                    /\ otsVer (Some pk) x.`2 x.`3 
                    /\ all (fun (e : int * message * sig) => e.`1 <= i /\ 0 < e.`1) tl 
                    /\ checkChain tl.


op tagVer (pk : pkey) (i : Time) (to : tag option) : bool
 = tagVerH pk i (tag2list (i, to)).




 
(* Correctness and Properties *)

lemma L_pl11: forall (pk : pkey) (i : int) (tg : tag option) (e : int *
                 message * sig) (es : (int * message * sig) list),
                 tagVer pk i tg = true =>
                 tag2list (i, tg) = e :: es => e.`1 = 1.
proof. smt. qed.


lemma L_pl4: forall (pk : pkey) (itg : int * tag option),
                tagVer pk itg.`1 itg.`2 = true =>
                exists (q1 : (int * message * sig) list) (m : message)
                  (s : sig), tag2list itg = q1 ++ [(itg.`1, m, s)].
proof. move => pk itg.
case (tag2list (itg.`1, itg.`2) = []).
smt.
move => h1.
have : exists q qs, tag2list (itg.`1, itg.`2) = q :: qs.
smt (oa2).
elim. move => q qs h2.
simplify tagVer. rewrite h2. simplify tagVerH.
have : exists z zs, q :: qs = zs ++ z :: []. 
smt (oa3).
elim. move => z zs h4.
have : (last q qs) = z. smt (oa4).
move => h5.
rewrite h5.
move => h6.
exists zs z.`2 z.`3. smt.
qed.


lemma L_pl9: forall (pk : pkey) (i : int) (tg : tag option) (q : (int *
                message * sig) list) (e : int * message * sig),
                tagVer pk i tg =>
                tag2list (i, tg) = e :: q =>
                otsVer (Some pk) e.`2 e.`3 = true.
proof. smt. qed.


lemma L_pl7': forall (pk : pkey) (i : int) (tg : tag option) (q1 : (int *
                message * sig) list) (e e' : int * message * sig)
                (q2 : (int * message * sig) list),
                checkChain (q1 ++ e :: e' :: q2) =>
                otsVer (msg2key e.`2 e'.`1) e'.`2 e'.`3 = true.
proof. move => pk i tg.
elim.  simplify checkChain. simplify msg2key. smt.
smt.
qed.


lemma L_pl7: forall (pk : pkey) (i : int) (tg : tag option) (q1 : (int *
                message * sig) list) (e e' : int * message * sig)
                (q2 : (int * message * sig) list),
                tagVer pk i tg =>
                tag2list (i, tg) = (q1 ++ e :: e' :: q2) =>
                otsVer (msg2key e.`2 e'.`1) e'.`2 e'.`3 = true.
proof. smt (L_pl7').
qed.


lemma L_pl8': forall (pk : pkey) (i : int) (tg : tag option) (e : int *
                 message * sig),
                 tagVer pk i tg = true =>
                 e \in tag2list (i, tg) => e.`1 <= i /\ 0 < e.`1.
proof. move => pk i tg e. simplify tagVer.
case ((tag2list (i, tg)) = []).
smt.
move => h.
have : exists x xs, tag2list (i, tg) = x::xs. smt (oa2).
elim. move => x xs.
move => h2. rewrite h2.
simplify tagVerH.
simplify checkPair. smt.
qed.



op infoAhead : int -> int = fun x => if x <= 0 then 0 else 2*x + 1.
op M : int = infoAhead EXP.        
lemma MNn : infoAhead EXP = M by auto.
lemma infoAheadP i :  0 <= i => i <= infoAhead i by smt.
lemma infoAheadM (i : int) j : 0 <= i => i <= j => infoAhead i <= infoAhead j by smt.
lemma infoAheadEXP (i : int) : i <= 0 => infoAhead i = 0 by smt.
lemma tdAx : forall (i : int), (i \in tdistr) => 0 < i by smt.
lemma Mpos : 1 <= M by smt.
lemma MEXP : EXP <= M by smt.
lemma dR_ll : is_lossless dR by smt.
lemma td_ll : is_lossless tdistr by smt.


lemma L_a5'': forall (sk1 sk2 : int -> skey option) (pk1 pk2 : int -> pkey option) 
 (i : int) (xs : int list), 
 (forall (j : int), j <= infoAhead i => sk1 j = sk2 j) =>
 (forall (j : int), j <= infoAhead i => pk1 j = pk2 j) =>
 (forall j, j \in xs => j <= i) =>
             0 < i => tagGen' pk1 sk1 xs = tagGen' pk2 sk2 xs.
proof.  move => sk1 sk2 pk1 pk2 i. elim. move => h1 h2 h3.
move => g. simplify delta. auto.
move => x l h1 h2 h3 j g.
simplify delta.
have : ((pk1 (2 * x) = pk2 (2 * x) /\ pk1 (2 * x + 1) = pk2 (2 * x + 1)) /\
 otsSig (odflt witness (sk1 x)) (x, pk1 (2 * x), pk1 (2 * x + 1)) =
 otsSig (odflt witness (sk2 x)) (x, pk2 (2 * x), pk2 (2 * x + 1))).
have : 2 * x + 1 <= infoAhead i. simplify infoAhead. timeout 20. smt.
smt.
move =>  k. rewrite k.
simplify.
apply h1.
smt. smt. 
progress. apply j. smt. auto.
qed.


lemma L_a5': forall (sk1 sk2 : int -> skey option) (i : int) ,
                       (forall (j : int), j <= infoAhead i => sk1 j = sk2 j) =>
                       tagGen sk1 i = tagGen sk2 i.
proof. simplify tagGen. move => sk1 sk2 i a1. 
case (i <= 0). auto.
move => q. congr.
apply (L_a5'' sk1 sk2 (fun (i0 : int) => omap sk2pk (sk1 i0)) 
                      (fun (i0 : int) => omap sk2pk (sk2 i0)) i). 
apply a1. smt. smt. smt.
qed.

lemma L_a5: forall (sk1 sk2 : int -> skey option) (i : int),
                       (forall (j : int), j <= infoAhead i => sk1 j = sk2 j) =>
                       tagGen sk1 i = tagGen sk2 i.
proof. move => sk1 sk2 i p. simplify tagGen. apply (L_a5' sk1 sk2 i). 
assumption.
qed.


lemma L_pl5: forall (pkf : int -> pkey option)(i e : int) (pk : pkey),
  msg2key (msg pkf i) e = Some pk => Some pk = pkf e.
proof. simplify msg2key. simplify msg. smt. qed.


lemma tagGenChainCorr3' skf  i: forall (xs : int list) r1 r2, 
 xs <> [] 
 => last r2 xs = i
 => (last r1 (tagGen' (fun (i0 : int) => omap sk2pk (skf i0)) skf xs)).`1 = i.
proof. elim. smt.
move => x1 l hyp r1 r2 p1  p2. 
case (l = []). move => q. rewrite q.
have : x1 = i. smt.
move => p. rewrite p. simplify tagGen'. simplify. trivial.
simplify tagGen'. move => q. 
apply (hyp ((x1, msg (fun (i0 : int) => omap sk2pk (skf i0)) x1,
            otsSig (oget (skf x1))
      (msg (fun (i0 : int) => omap sk2pk (skf i0)) x1))) x1 q p2)  .
qed.


lemma tagGenChainCorr3 skf  i: 0 < i =>
  (last witness (tagGen' (fun (i0 : int) => omap sk2pk (skf i0)) skf (binRec i))).`1 = i.
proof. move => q. 
apply (tagGenChainCorr3' skf i (binRec i) witness witness).
smt. smt.
qed.


lemma tagGenChainCorr2' skf i: forall (xs : int list), 
 (forall x, x \in xs => x <= i /\ 0 < x)
  => all (fun (e : int * message * sig) => e.`1 <= i /\ 0 < e.`1)
         (tagGen' (fun (i0 : int) => omap sk2pk (skf i0)) skf xs).
proof. elim. simplify. smt.
simplify. move => n p1 p2 p3. 
simplify tagGen'. simplify. 
have : (n <= i /\ 0 < n) = true.
have : (n <= i /\ 0 < n). apply (p3 n). smt.
move => q. rewrite q. simplify. auto.
progress. smt. smt. apply p2. smt.
qed.


lemma tagGenChainCorr2 skf i: 
  all (fun (e : int * message * sig) => e.`1 <= i /\ 0 < e.`1)
  (tagGen' (fun (i0 : int) => omap sk2pk (skf i0)) skf (binRec i)).
proof. apply tagGenChainCorr2'. apply (br3).
qed.


lemma tagGenChainCorr1 pkf skf : 
  forall (xs : int list), 
  (forall j, exists pk sk rs, pkf j = Some pk /\ skf j = Some sk /\ (pk, sk) = otsKey rs) 
 => (forall xs1 xs2 e e', xs = xs1 ++ e :: e' :: xs2 => e = div e' 2)  =>
   checkChain (tagGen' pkf skf xs) = true.
elim. smt.
move => x. elim.
move =>_ _ _. simplify delta. simplify. trivial.
move => h1 h2 h3 h4 h5 h6.
simplify tagGen'. simplify.
have : ((foldr
   (fun (n : int) (r : (int * (int * pkey option * pkey option) *
      sig) list) => (n, msg pkf n, otsSig (oget (skf n)) (msg pkf n)) :: r)
   [] h2 <>
 [] =>
 checkPair
   (head witness
      (foldr
         (fun (n : int) (r : (int * (int * pkey option * pkey option) *
            sig) list) =>
            (n, msg pkf n, otsSig (oget (skf n)) (msg pkf n)) :: r) [] h2))
   (h1, msg pkf h1, otsSig (oget (skf h1)) (msg pkf h1))) /\
checkChain
  (foldr
     (fun (n : int) (r : (int * (int * pkey option * pkey option) *
        sig) list) => (n, msg pkf n, otsSig (oget (skf n)) (msg pkf n)) :: r)
     [] h2)) = checkChain (tagGen' pkf skf (h1 :: h2)).
simplify tagGen'. auto.
move => qq.
rewrite  qq.
have : checkChain (tagGen' pkf skf (h1 :: h2)) = true.
apply h4. smt. move => xs1 xs2 e e' o. 
case (xs1 = []).
move => q.
apply (h6 (x :: []) xs2). smt.
move => q.
apply (h6 (x :: xs1) xs2). smt.
move => hz. rewrite hz. simplify.
simplify delta.
have : x = div h1 2. apply (h6 [] h2). auto.
move => z. rewrite z.
case (h1 = (2 * (div h1 2) + 1)). 
move => w. rewrite w.
rewrite (div3 (div h1 2)).
simplify.
have : (2 * div h1 2 + 1 = 2 * div h1 2) = false. smt.
move => oo. rewrite oo. simplify.
have : exists pk sk rs, pkf (2 * div h1 2 + 1) = Some pk /\ skf (2 * div h1 2 + 1) = Some sk 
 /\ (pk, sk) = otsKey rs.
apply h5.
elim.
move => pk sk rs.
elim. move => e1. elim. move => e2 e3.
rewrite e1 e2. simplify.
apply (otsCorrect rs pk sk). apply e3.
move => u.
have : (h1 = (2 * (div h1 2))).  apply div4. apply u.
move => q. rewrite q.
rewrite (div2 (div h1 2)).
have : (2 * div h1 2 = 2 * div h1 2) = true. reflexivity.
move => qc. rewrite qc. simplify.
have : exists pk sk rs, pkf (2 * div h1 2) = Some pk 
             /\ skf (2 * div h1 2) = Some sk /\ (pk, sk) = otsKey rs.
apply h5.
elim.
move => pk sk rs.
elim. move => e1. elim. move => e2 e3.
rewrite e1 e2. simplify.
apply (otsCorrect rs pk sk). apply e3.
qed.



op tagGenS : (int -> pkey option) ->  (int, sig) fmap  -> int list -> tag = 
  fun pkf skf xs => foldr (fun n r => 
        (n, (msg pkf n), oget skf.[n]) :: r) [] xs.

      
lemma zup pkf skf fm : forall (xs : int list), 
 (forall j, j \in xs => otsSig (oget (skf j)) (msg pkf j) = (oget fm.[j]))
 => tagGen' pkf skf xs = tagGenS pkf fm xs.
proof. elim.
smt.
move => x l hyp h.
simplify tagGen' tagGenS.
have : (otsSig (oget (skf x)) (msg pkf x) = oget fm.[x]) = true.
smt.
move => q. rewrite q. simplify.
apply hyp. smt.
qed.


lemma multTagsCorrect skf : 
   (forall j, exists pk sk rs, omap sk2pk (skf j) = Some pk 
               /\ skf j = Some sk /\ (pk, sk) = otsKey rs)  =>
   forall i, 0 < i => tagVer (oget (omap sk2pk (skf 1))) i (tagGen skf i).
move => jp i p.  
simplify tagVer .
have : i <= 0 = false. smt. move => co.
have : ((tag2list (i, tagGen  skf i)) <> []).
simplify tagGen. rewrite co.  simplify.  simplify tag2list oget. 
have : exists xs, (binRec i) = (1 :: xs). apply br4. apply p.
elim. move => xs pq. rewrite pq. simplify tagGen'. auto.
move => h. 
have : exists x xs, (tag2list (i, tagGen skf i)) = x::xs. smt (oa2).
elim. move => x xs.
move => h1.
rewrite h1.
simplify .
have : ((xs <> [] => checkPair (head witness xs) x) /\ checkChain xs) = checkChain (x::xs). smt.
move => g.
rewrite g.
rewrite - h1.
have : ((x.`1 <= i /\ 0 < x.`1) /\
   all (fun (e : int * message * sig) => e.`1 <= i /\ 0 < e.`1) xs) 
 = all (fun (e : int * message * sig) => e.`1 <= i /\ 0 < e.`1) 
       (tag2list (i, tagGen skf i)).
smt. move => ol. rewrite ol.
have : x.`1 = 1.
have : x = head witness (tag2list (i, tagGen skf i)). smt.
move => zo. rewrite zo.
simplify tag2list. simplify tagGen.
rewrite co. simplify. simplify oget.
have : exists xs, (binRec i) = (1 :: xs). apply br4. apply p.
elim. move => zs pq. rewrite pq. simplify tagGen'. auto.
have : (last witness (tag2list (i, tagGen skf i))).`1 = i. 
simplify tag2list. simplify tagGen.
rewrite co. simplify. simplify oget. apply tagGenChainCorr3. smt.
move => ff. progress.
have : (last x xs) = last witness (tag2list (i, tagGen skf i)). smt.
move => zo. rewrite zo.
apply ff.
have : head witness (tag2list (i, tagGen skf i)) = (1, (msg (fun (i0 : int) 
 => omap sk2pk (skf i0)) 1), otsSig (oget (skf 1)) 
     (msg (fun (i0 : int) => omap sk2pk (skf i0)) 1)).
simplify tag2list. simplify tagGen. rewrite co. simplify. simplify oget.
have : exists xs, (binRec i) = (1 :: xs). apply br4. apply p.
elim. move => xss pq. rewrite pq. simplify tagGen'. auto.
move => qp.
have : x = (1, (msg (fun (i0 : int) => omap sk2pk (skf i0)) 1), 
   otsSig (oget (skf 1)) (msg (fun (i0 : int) => omap sk2pk (skf i0)) 1)). smt.
move => qp1. rewrite qp1. simplify delta. 
have : exists (pk : pkey) (sk : skey) (rs : int),
        (fun (i0 : int) => omap sk2pk (skf i0)) 1 = Some pk 
  /\ skf 1 = Some sk /\ (pk, sk) = otsKey rs. apply (jp 1). elim.
move => pk sk rs p1. smt.
simplify tag2list tagGen. rewrite co. simplify. simplify oget.
apply tagGenChainCorr2.
simplify tag2list. simplify tagGen.  rewrite co. simplify. simplify oget.
have : checkChain
  (tagGen' (fun (i0 : int) => omap sk2pk (skf i0)) skf (binRec i)) = true.
apply (tagGenChainCorr1 (fun i => omap sk2pk (skf i)) skf (binRec i)).
smt. apply br5.
smt. smt.
qed.
