
(* Theory which formalizes the pre-image resistance of the hash functions *)
abstract theory Hash_Theory.

type r.
op h : r -> r.
op rDistr : r distr.


module type AdvPRE = {
  proc forge(v : r) : r
}.


module GamePRE(A : AdvPRE) = {
  proc main() = {
    var r1, r2;
    r1 <$ rDistr;
    r2 <@ A.forge(h r1);
    return h r2 = h r1;
  }
}.


end Hash_Theory.
