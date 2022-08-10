require import Distr Int.

abstract theory KeyGen.

type pkey, skey.

module type KeyGenT = {
  proc keyGen() : pkey * skey
}.


(* Simple key generation module  *)
op dR : int distr.
op keyGen : int -> (pkey * skey).
module SimpleKeyGen : KeyGenT = {
  proc keyGen() : pkey * skey = {
    var r;
    r <$ dR;
    return keyGen r;
  }
}.

end KeyGen.
