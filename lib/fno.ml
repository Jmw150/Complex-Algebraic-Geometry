(** High-level float API for the Fourier Neural Operator. *)

open Complexrocq
open Fnorocq

(* ------------------------------------------------------------------ *)
(* Type aliases                                                         *)
(* ------------------------------------------------------------------ *)

type complex_f = float * float
type signal = complex_f list

(* ------------------------------------------------------------------ *)
(* Conversion helpers                                                   *)
(* ------------------------------------------------------------------ *)

let of_signal (s : signal) : cComplex list =
  List.map (fun (r, i) -> ccomplex_of_floats r i) s

let to_signal (cs : cComplex list) : signal =
  List.map floats_of_ccomplex cs

let real_signal (xs : float list) : signal =
  List.map (fun x -> (x, 0.0)) xs

(* ------------------------------------------------------------------ *)
(* FNO layer / network constructors                                     *)
(* ------------------------------------------------------------------ *)

let make_layer
    ~(k_max : int)
    ~(weights : signal)
    ~(skip : complex_f)
    ~(nonlin : cComplex -> cComplex)
    : fNOLayerParams =
  { fno_K_max  = nat_of_int k_max;
    fno_weights = of_signal weights;
    fno_skip    = ccomplex_of_floats (fst skip) (snd skip);
    fno_nonlin  = nonlin }

let make_fno
    ~(lift : complex_f)
    ~(proj : complex_f)
    ~(layers : fNOLayerParams list)
    : fNOParams =
  { fno_lift   = ccomplex_of_floats (fst lift) (snd lift);
    fno_proj   = ccomplex_of_floats (fst proj) (snd proj);
    fno_layers = layers }

(* ------------------------------------------------------------------ *)
(* Nonlinearities                                                       *)
(* ------------------------------------------------------------------ *)

let id_nonlin : cComplex -> cComplex = fun z -> z

let relu : cComplex -> cComplex = relu_c

let tanh_nonlin : cComplex -> cComplex = fun z ->
  let (r, i) = floats_of_ccomplex z in
  ccomplex_of_floats (tanh r) i

(* ------------------------------------------------------------------ *)
(* Forward pass                                                         *)
(* ------------------------------------------------------------------ *)

let dft (s : signal) : signal =
  to_signal (Fnorocq.dft (of_signal s))

let idft (s : signal) : signal =
  to_signal (Fnorocq.idft (of_signal s))

let forward (net : fNOParams) (input : signal) : signal =
  to_signal (fno_forward net (of_signal input))

let layer_forward (lp : fNOLayerParams) (input : signal) : signal =
  to_signal (fno_layer lp (of_signal input))

let cyclic_conv (xs : signal) (ys : signal) : signal =
  to_signal (Fnorocq.cyclic_conv (of_signal xs) (of_signal ys))

(* ------------------------------------------------------------------ *)
(* Printing                                                             *)
(* ------------------------------------------------------------------ *)

let string_of_complex (r, i) =
  if Float.abs i < 1e-9 then Printf.sprintf "%.6f" r
  else if i >= 0.0 then Printf.sprintf "%.6f+%.6fi" r i
  else Printf.sprintf "%.6f%.6fi" r i

let print_signal label (s : signal) =
  Printf.printf "%s: [%s]\n" label
    (String.concat ", " (List.map string_of_complex s))
