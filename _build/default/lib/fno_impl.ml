(** OCaml implementations of the axiomatized CReal primitives needed
    by the Fourier Neural Operator extraction.

    We use float arithmetic internally with 9-decimal-place injection back
    into CReal (sufficient for FNO demo computations). *)

open Complexrocq

(* ------------------------------------------------------------------ *)
(* Minimal nat/positive/z helpers (avoid depending on Converters)      *)
(* ------------------------------------------------------------------ *)

let rec pos_of_int n =
  if n <= 1 then XH
  else if n land 1 = 0 then XO (pos_of_int (n lsr 1))
  else XI (pos_of_int (n lsr 1))

let rec int_of_pos = function
  | XH -> 1
  | XO p -> 2 * int_of_pos p
  | XI p -> 2 * int_of_pos p + 1

let z_of_int n =
  if n = 0 then Z0
  else if n > 0 then Zpos (pos_of_int n)
  else Zneg (pos_of_int (-n))

let int_of_z = function
  | Z0 -> 0
  | Zpos p -> int_of_pos p
  | Zneg p -> -(int_of_pos p)

(* ------------------------------------------------------------------ *)
(* float <-> q <-> CReal                                               *)
(* ------------------------------------------------------------------ *)

let float_of_q q =
  float_of_int (int_of_z q.qnum) /. float_of_int (int_of_pos q.qden)

(** Convert float to rational with 9 decimal places of precision. *)
let q_of_float f =
  let scale = 1_000_000_000 in
  let n = int_of_float (Float.round (f *. float_of_int scale)) in
  { qnum = z_of_int n; qden = pos_of_int scale }

(** Extract a float approximation from a CReal (using prec ≈ 2^{-30}). *)
let float_of_creal x =
  let prec = Zneg (pos_of_int 30) in
  float_of_q (approx x prec)

(** Inject a float into CReal via rational approximation. *)
let creal_of_float f = inject_Q (q_of_float f)

(** Inject a float pair into CComplex. *)
let ccomplex_of_floats r i =
  { re = creal_of_float r; im = creal_of_float i }

(** Extract float pair from CComplex (at 2^{-20} precision). *)
let floats_of_ccomplex c =
  (float_of_creal c.re, float_of_creal c.im)

(* ------------------------------------------------------------------ *)
(* Implementations of the axiomatized primitives                       *)
(* ------------------------------------------------------------------ *)

(** exp_i θ = (cos θ) + i·(sin θ), computed via OCaml float. *)
let exp_i_impl theta =
  let t = float_of_creal theta in
  ccomplex_of_floats (cos t) (sin t)

(** π as a CReal (injected from Float.pi ≈ 3.14159265358979...). *)
let pi_r_impl = creal_of_float Float.pi
