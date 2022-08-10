require import Int Bool SmtMap Distr.

abstract theory Timestamping.

(* data and tdistr are parameters of this theory *)
type data.
op   tdistr : int distr.

type Time = int.

(* interface of timestamping services *)
module type Repo = {
  proc init()                   : unit
  proc clock()                    : Time
  proc put(d : data)              : Time
  proc check(t : Time, d : data)  : bool
}.


(* simplest and "obviously" correct instance of Repo *)
module Ts : Repo = {
  var r : (Time, data) fmap  (* finite map of "timestamped" *)
  var i : Time               (* initial time *)
  var t : Time               (* current time *)  
  proc init() = {
    i <$ tdistr;             (* initial time is sampled from tdistr *)
    t <- i;
    r <-  empty<:Time, data>; (* initially the map is empty *)
  }  
  proc clock() = {
    return t;
  }    
  proc put(d : data) = {
     t <- t + 1;
     r <- r.[t <- d];
     return t;
  }  
  proc check(t : Time, d : data) = {
    return r.[t] = Some d;
  }  
}.

end Timestamping.
