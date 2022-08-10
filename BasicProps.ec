require import Int  Bool Distr AllCore List SmtMap IntDiv DInterval.


lemma slz ['a] p  : forall (xs : 'a list), has p xs 
  => exists q1 e q2, xs = q1 ++ e :: q2 /\ (forall e, e \in q2 => !p e) /\ p e  .
proof. apply last_ind.
move => s . smt.
move => s x h s0.
case (p x).
move => px.
exists s x [].
smt.
move => px. 
have : has p s. smt.
move => hh.
have : exists (q1 : 'a list) (e : 'a) (q2 : 'a list),
         s = q1 ++ e :: q2 /\ (forall (e0 : 'a), e0 \in q2 => ! p e0) /\ p e. 
apply (h hh).
elim. move => q1 e q2 hs.
exists q1 e (rcons q2 x).
progress. smt. smt. smt.
qed.


(* odflt . omap *)
op odfltmap ['a 'b] (d : 'b) (f : 'a -> 'b)
  (ox : 'a option) : 'b = 
  with ox = None => d
  with ox = Some x => f x.


(* uniform distrib *)
lemma ddi (p M : int) : p <= M => 1 <= p 
 => mu (dinter 1 M) (fun (x : int) => p = x) = inv M%r.
proof. move => c1 c2. 
have : mu1 (dinter 1 M) p =  1%r/(M - 1 + 1)%r. smt.
smt.
qed.


lemma ddi' (p M : int) : p <= M => 1 <= p 
 => mu (dinter 1 M) (fun (x : int) => x = p) = inv M%r.
proof. move => c1 c2. 
have : mu1 (dinter 1 M) p =  1%r/(M - 1 + 1)%r. smt.
smt.
qed.

lemma ddl (M : int) : 0 < M => is_lossless (dinter 1 M).
proof. smt. qed.

(* division facts *)
op div : int -> int -> int = (%/).

lemma div0 : forall (x : int), exists y r, (x = y * 2 + r) /\ 0 <= r < 2.
proof. smt. qed.

lemma div1 : forall (x : int), exists y, (x = y * 2 + 1) ^ (x = y * 2).
proof. smt (div0). qed.

lemma div2 : forall (x : int), div (2 * x) 2 = x. 
proof. smt. qed.

lemma div3 : forall (x : int), div (2 * x + 1) 2 = x.
proof. smt. qed.

lemma div4 : forall (x : int), x <> 2 * div x 2 + 1 => x = 2 * div x 2.
proof. smt. qed.

lemma if1 : forall (i j x : int), i <= j => i + x <= j + x.
proof. smt.
qed.

lemma o11 (m : ('a, 'b) fmap) n a b : m.[n <- a].[n <- b] = m.[n <- b].
proof. apply set_set_sameE.
qed.

lemma oa5 ['a] x : forall (p : 'a list),  head x p = last x (rev p).
proof. elim.  simplify rev. smt.
smt.
qed.

lemma oa6 ['a] x : forall (p : 'a list),  last x p = head x (rev p).
proof. elim.  simplify rev. smt.
smt.
qed.

lemma oa7 ['a] (pr : 'a -> bool) : forall (p : 'a list), 
 all pr p => all pr (rev p).
proof. elim. smt. smt.
qed.

lemma oa8 ['a] : forall (p : 'a list),  p <> []  => (rev p) <> [].
proof. elim. smt. smt.
qed.

lemma oa9 ['a] x : forall (p : 'a list),  head x (rev p) = last x p.
proof. elim.  simplify rev. smt.
smt.
qed.

lemma oa10 ['a] x : forall (p : 'a list),  last x (rev p) = head x p.
proof. elim.  simplify rev. smt.
smt.
qed.

lemma oa1 ['a] (p : 'a option) : p <> None => exists x, p = Some x.
elim p. smt. smt.
qed.

lemma oa2 ['a] (p : 'a list) : p <> [] => exists x xs, p = x :: xs.
elim p. smt. smt.
qed.

lemma oa3 ['a] : forall (p : 'a list), p <> [] => exists x xs, p = xs ++ [x].
proof. elim.
smt. smt (@List).
qed.

lemma oa4 ['a] e z  : forall (zs : 'a list), last e (zs ++ [z]) = z.
proof. elim. smt.
smt.
qed.


(* "binRec t" must compute the indices of parents of the  t-th node *)
op binRec : int -> int list.

(* axiomatization of binRec *)
(* the root and zero cases *)
axiom br6   : binRec 1 = [1]. 
axiom br0   : binRec 0 = [].  
(* parents list always contains a root *)
axiom br1 i : 0 < i => head 0 (binRec i) = 1.
(* parents list always contains the element itself *)
axiom br2 i : 0 < i => last 0 (binRec i) = i.
(* nodes in the list are in the range form 1 to i *)
axiom br3 i : forall j, j \in (binRec i) => j <= i /\ 0 < j.
(* list of parents starts with the root *)
axiom br4 i : 0 < i => exists xs, binRec i = 1 :: xs.
(* the two adjoint elements e and e' are related by equation e = div e' 2 *)
axiom br5 i : 0 < i => forall (xs1 xs2 : int list) (e e' : int),
  binRec i = xs1 ++ e :: e' :: xs2 => e = div e' 2.

