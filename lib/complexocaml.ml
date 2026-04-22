
(* Complex rationals: Q[i] implemented on top of Zarith *)

(* could also use Qi, but we are using a subset of C anyway *)
module C : sig
  type t = { re : Q.t ; im : Q.t } 

  (* Default values *)
  val zero : t
  val one : t

  (* maps from other structures *)
  val of_qs  : Q.t -> Q.t -> t
  val of_q  : Q.t -> t
  val of_int : int -> t
  val of_ints : int -> int -> t
  val of_z  : Z.t -> t

  val equal   : t -> t -> bool

  val neg  : t -> t
  val conj : t -> t

  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t

  val norm2 : t -> Q.t          (* re^2 + im^2 *)
  val inv   : t -> t            (* fails on 0 *)
  val div   : t -> t -> t       (* fails on divisor 0 *)

  val to_string : t -> string

  module Infix : sig
    val ( + ) : t -> t -> t
    val ( - ) : t -> t -> t
    val ( * ) : t -> t -> t
    val ( / ) : t -> t -> t
  end

end = struct 
  type t = { re : Q.t ; im : Q.t } 

  let zero = { re = Q.zero; im = Q.zero }
  let one  = { re = Q.one;  im = Q.zero }
  let i    = { re = Q.zero; im = Q.one  }

  (* all sorts of constructors *)
  let of_qs a b = { re = a ; im = b }
  let of_q a = { re = a ; im = Q.of_int 0 }
  let of_ints a b = { (* int is not an integer *)
    re = Q.of_int a; 
    im = Q.of_int b
  }
  let of_int a = { (* int is not an integer *)
    re = Q.of_int a; 
    im = Q.of_int 0
  }
  let of_z z     = { re = Q.of_bigint z; im = Q.zero }

  (* projections *)
(*  let re z = z.re*)
(*  let im z = z.im*)

  (* needed for testing *)
  let equal a b = Q.equal a.re b.re && Q.equal a.im b.im

(*  let%test "make" = equal (of_ints 1 2) (of_ints 1 2) *)
    

  let add a b = { re = Q.add a.re b.re ; im = Q.add a.im b.im}
  let sub a b = { re = Q.sub a.re b.re ; im = Q.sub a.im b.im}

  let neg a = { re = Q.neg a.re ; im = Q.neg a.im}

  let mul z q = 
  (* (a+bi)(c+di) = ac+adi+bci-bd = (ac - bd) + (ad + bc)i *)
    let ac = Q.mul z.re q.re in
    let bd = Q.mul z.im q.im in
    let ad = Q.mul z.re q.im in
    let bc = Q.mul z.im q.re in
    { re = Q.sub ac bd ; im = Q.add ad bc}

  let norm2 z =
    Q.add (Q.mul z.re z.re) (Q.mul z.im z.im)

  let conj a = { re = a.re ; im = Q.neg a.im }

  let inv z =
    let d = norm2 z in
    if Q.equal d Q.zero then invalid_arg "C.inv: division by zero";
    (* 1/(a+bi) = (a-bi)/(a^2+b^2) *)
    let c = conj z in
    { re = Q.div c.re d; im = Q.div c.im d }

  let div a b = mul a (inv b)
      
  let to_string z = 
    if Q.equal z.re Q.zero then
      if Q.equal z.im Q.zero then "0"
      else Q.to_string z.im ^ "i"
    else if Q.equal z.im Q.zero then Q.to_string z.re
    else if Q.lt z.im Q.zero then Q.to_string z.re ^ " " ^ Q.to_string z.im ^ "i"
    else Q.to_string z.re ^ "+" ^ Q.to_string z.im ^ "i"


module Infix = struct
    let ( + ) = add
    let ( - ) = sub
    let ( * ) = mul
    let ( / ) = div
    let ( ~- ) = neg
  end
end
