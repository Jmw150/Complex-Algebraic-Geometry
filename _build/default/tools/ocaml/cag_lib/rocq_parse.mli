(** Rocq file parser — extracts top-level declarations from .v files.

    Not a full Rocq parser; uses regex on a comment-stripped buffer plus
    a brace-balanced scan for statement-end. Good enough for indexing. *)

type kind =
  | Theorem
  | Lemma
  | Corollary
  | Proposition
  | Fact
  | Remark
  | Definition
  | Fixpoint
  | CoFixpoint
  | Axiom
  | Parameter
  | Hypothesis
  | Conjecture
  | Example
  | Inductive
  | CoInductive
  | Class
  | Instance
  | Record
  | Structure
  | Variant

val string_of_kind : kind -> string
val kind_of_string : string -> kind option
val all_kinds : kind list

type declaration = {
  name : string;
  kind : kind;
  statement : string;  (** Full statement up to the terminating `.` *)
  file : string;       (** Absolute or relative path *)
  line : int;          (** 1-based line where the declaration begins *)
}

val strip_comments : string -> string
(** Replace [(*...*)] (nested-aware) with whitespace; preserves line numbers. *)

val iter_declarations : string -> declaration list
(** Parse a single file. Returns declarations in document order. *)

val walk_theories : string -> declaration Seq.t
(** Recursively walk all [.v] files under [root]. Skips [_build/], [lib/], [.git/]. *)
