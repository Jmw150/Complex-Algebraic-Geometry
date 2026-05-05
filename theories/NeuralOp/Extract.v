(** * NeuralOp/Extract.v
    Extraction directives for the Fourier Neural Operator.

    The two axiomatized primitives are given concrete OCaml implementations:
      - exp_i θ  ↦  (cos θ, sin θ)  via OCaml's Float.cos / Float.sin
      - pi_R     ↦  Float.pi        as a rational-approximated CReal

    Both use float arithmetic internally; the results are injected back
    into CReal as rational constants with 9 decimal digits of precision.
    This is more than enough for FNO demo computations. *)

From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import QArith ZArith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyAbs.

From CAG Require Import Complex.
From CAG Require Import NeuralOp.DFT.
From CAG Require Import NeuralOp.FNO.

Extraction Language OCaml.

(* CAG constructive-remove Extraction NeuralOpExtract theories/NeuralOp/Extract.v:25 BEGIN
(** Map the axiomatized exp_i to an OCaml implementation in Fno_impl. *)
Extract Constant exp_i => "Fno_impl.exp_i_impl".

(** Map the axiomatized pi_R to an OCaml value in Fno_impl. *)
Extract Constant pi_R => "Fno_impl.pi_r_impl".

(** Extract the core DFT and FNO functions. *)
Extraction "lib/fnorocq.ml"
  omega
  dft
  idft
  spectral_proj
  low_pass
  truncate_modes
  pad_to
  cyclic_conv
  pointwise_mul
  csum
  nth_C
  relu_C
  apply_nonlin
  fno_layer
  fno_forward
  apply_layers
  spectral_conv
  skip_connection
  lift
  circulant_op.
   CAG constructive-remove Extraction NeuralOpExtract theories/NeuralOp/Extract.v:25 END *)
