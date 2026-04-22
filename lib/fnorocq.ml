(** Extracted Fourier Neural Operator (DFT + FNO).
    All CReal/CComplex/nat/z/q infrastructure comes from Complexrocq. *)

open Complexrocq

(* ------------------------------------------------------------------ *)
(* Conversion helpers (return local types for use in fno.ml)           *)
(* ------------------------------------------------------------------ *)

let rec nat_of_int n = if n <= 0 then O else S (nat_of_int (n - 1))

let ccomplex_of_floats r i = Fno_impl.ccomplex_of_floats r i

let floats_of_ccomplex c = Fno_impl.floats_of_ccomplex c

(* ------------------------------------------------------------------ *)
(* Utility functions not exported by Complexrocq                       *)
(* ------------------------------------------------------------------ *)

(** Pos.of_nat: convert nat to positive (0 → XH) *)
let rec pos_of_nat = function
  | O -> XH
  | S O -> XH
  | S n -> Coq_Pos.succ (pos_of_nat n)

module Coq_Pos = struct
  include Complexrocq.Coq_Pos
  let of_nat = pos_of_nat
end

let rec mul n m =
  match n with
  | O -> O
  | S p -> add (mul p m) m

let rec seq start = function
| O -> []
| S len0 -> start :: (seq (S start) len0)

let rec nth n l default =
  match n with
  | O -> (match l with | [] -> default | x :: _ -> x)
  | S m -> (match l with | [] -> default | _ :: t -> nth m t default)

let rec firstn n l =
  match n with
  | O -> []
  | S n0 -> (match l with | [] -> [] | a :: l0 -> a :: (firstn n0 l0))

let rec combine l l' =
  match l with
  | [] -> []
  | x :: tl ->
    (match l' with | [] -> [] | y :: tl' -> (x, y) :: (combine tl tl'))

module Nat = struct
  let rec sub n m =
    match n with
    | O -> n
    | S k -> (match m with | O -> n | S l -> sub k l)

  let rec divmod x y q u =
    match x with
    | O -> (q, u)
    | S x' ->
      (match u with
       | O -> divmod x' y (S q) y
       | S u' -> divmod x' y q u')

  let modulo x = function
  | O -> x
  | S y' -> sub y' (snd (divmod x y' O y'))
end

let sub = Nat.sub

(* ------------------------------------------------------------------ *)
(* CReal absolute value and max (not in Complexrocq)                   *)
(* ------------------------------------------------------------------ *)

let cReal_abs_seq x n = qabs (x.seq n)
let cReal_abs_scale x = x.scale
let cReal_abs x = { seq = cReal_abs_seq x; scale = cReal_abs_scale x }

let cReal_max x y =
  cReal_mult (cReal_plus (cReal_plus x y) (cReal_abs (cReal_minus y x)))
    (inject_Q { qnum = (Zpos XH); qden = (XO XH) })

(** val cpow : cComplex -> nat -> cComplex
    Float-based to avoid O(2^n) CReal tree depth. **)

let int_of_nat_local n =
  let rec go acc = function O -> acc | S k -> go (acc + 1) k in
  go 0 n

let cpow z0 n =
  let (r, i) = floats_of_ccomplex z0 in
  let theta = atan2 i r in
  let mag   = sqrt (r *. r +. i *. i) in
  let nf    = float_of_int (int_of_nat_local n) in
  let rn    = mag ** nf in
  let tn    = nf *. theta in
  ccomplex_of_floats (rn *. cos tn) (rn *. sin tn)

(** Eagerly evaluate a cComplex to floats and re-inject, resetting CReal depth. **)

let normalize_cc c =
  let (r, i) = floats_of_ccomplex c in
  ccomplex_of_floats r i

(** val exp_i : cReal -> cComplex **)

let exp_i = Fno_impl.exp_i_impl

(** val pi_R : cReal **)

let pi_R = Fno_impl.pi_r_impl

(** val omega : nat -> cComplex **)

let omega n =
  exp_i
    (cReal_opp
      (cReal_mult
        (cReal_mult (inject_Q { qnum = (Zpos (XO XH)); qden = XH }) pi_R)
        (inject_Q { qnum = (Zpos XH); qden = (Coq_Pos.of_nat n) })))

(** val csum : nat -> (nat -> cComplex) -> cComplex **)

let rec csum n f =
  match n with
  | O -> c0
  | S n0 -> cadd (csum n0 f) (f n0)

(** val nth_C : cComplex list -> nat -> cComplex **)

let nth_C xs n =
  nth n xs c0

(** val dft_coeff : cComplex list -> nat -> cComplex **)

let dft_coeff xs k =
  let n = length xs in
  normalize_cc (csum n (fun n0 -> cmul (nth_C xs n0) (cpow (omega n) (mul n0 k))))

(** val dft : cComplex list -> cComplex list **)

let dft xs =
  map (dft_coeff xs) (seq O (length xs))

(** val idft_coeff : cComplex list -> nat -> cComplex **)

let idft_coeff xs n =
  let n0 = length xs in
  let inv_N = cinject_Q { qnum = (Zpos XH); qden = (Coq_Pos.of_nat n0) } in
  normalize_cc (cmul inv_N
    (csum n0 (fun k ->
      cmul (nth_C xs k) (cpow (omega n0) (sub (mul n0 k) (mul n k))))))

(** val idft : cComplex list -> cComplex list **)

let idft xs =
  map (idft_coeff xs) (seq O (length xs))

(** val cyclic_conv : cComplex list -> cComplex list -> cComplex list **)

let cyclic_conv xs ys =
  let n = length xs in
  map (fun n0 ->
    csum n (fun m ->
      cmul (nth_C xs m)
        (nth_C ys (Nat.modulo (sub (add n0 n) (Nat.modulo m n)) n))))
    (seq O n)

(** val pointwise_mul : cComplex list -> cComplex list -> cComplex list **)

let pointwise_mul xs ys =
  map (fun pat -> let (x, y) = pat in cmul x y) (combine xs ys)

(** val truncate_modes : nat -> cComplex list -> cComplex list **)

let truncate_modes =
  firstn

(** val pad_to : nat -> cComplex list -> cComplex list **)

let pad_to n xs =
  app xs (repeat c0 (sub n (length xs)))

(** val low_pass : nat -> nat -> cComplex list -> cComplex list **)

let low_pass n k_max xs =
  pad_to n (truncate_modes k_max xs)

(** val spectral_proj : nat -> cComplex list -> cComplex list **)

let spectral_proj k_max xs =
  idft (low_pass (length xs) k_max (dft xs))

type nonlinearity = cComplex -> cComplex

(** val relu_c : nonlinearity **)

let relu_c z0 =
  { re = (cReal_max z0.re (inject_Q { qnum = Z0; qden = XH })); im = z0.im }

(** val apply_nonlin : nonlinearity -> cComplex list -> cComplex list **)

let apply_nonlin =
  map

type fNOLayerParams = { fno_K_max : nat; fno_weights : cComplex list;
                        fno_skip : cComplex; fno_nonlin : nonlinearity }

(** val apply_weights : cComplex list -> cComplex list -> cComplex list **)

let apply_weights =
  pointwise_mul

(** val spectral_conv : fNOLayerParams -> cComplex list -> cComplex list **)

let spectral_conv p v =
  let n = length v in
  let xfull = dft v in
  let xlow = truncate_modes p.fno_K_max xfull in
  let xweighted = apply_weights p.fno_weights xlow in
  let xpad = pad_to n xweighted in idft xpad

(** val skip_connection : fNOLayerParams -> cComplex list -> cComplex list **)

let skip_connection p v =
  map (fun x -> cmul p.fno_skip x) v

(** val fno_layer : fNOLayerParams -> cComplex list -> cComplex list **)

let fno_layer p v =
  let kv = spectral_conv p v in
  let wv = skip_connection p v in
  apply_nonlin p.fno_nonlin
    (map (fun pat -> let (k, w) = pat in cadd k w) (combine kv wv))

type fNOParams = { fno_lift : cComplex; fno_proj : cComplex;
                   fno_layers : fNOLayerParams list }

(** val lift : cComplex -> cComplex list -> cComplex list **)

let lift p v =
  map (cmul p) v

(** val apply_layers :
    fNOLayerParams list -> cComplex list -> cComplex list **)

let rec apply_layers layers v =
  match layers with
  | [] -> v
  | l :: ls -> apply_layers ls (fno_layer l v)

(** val fno_forward : fNOParams -> cComplex list -> cComplex list **)

let fno_forward p u =
  lift p.fno_proj (apply_layers p.fno_layers (lift p.fno_lift u))

(** val circulant_op : cComplex list -> cComplex list -> cComplex list **)

let circulant_op =
  cyclic_conv
