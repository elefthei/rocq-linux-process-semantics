(** * A bounded common representation for the two exit arms

    Rocq reads the file [exit.hex] directly. Each theorem
    relates the existing spec to this interpretation of
    that file. *)

From Stdlib Require Import ZArith List Bool Lia PrimString.
From ReadFile Require Import ReadFile.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase State Monad Specs RiscvSemantics.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** Byte literals bound the common syntax, not the production specification
    or its raw 64-bit syscall arguments. *)
Inductive Clause :=
  | halt (argument mask result : byte)
  | decline.

Definition serialize (c : Clause) : list byte :=
  match c with
  | halt argument mask result => [Z_to_bv 8 0; argument; mask; result]
  | decline => [Z_to_bv 8 1]
  end.

Definition deserialize (bs : list byte) : option Clause :=
  match bs with
  | [tag; argument; mask; result] =>
      if bv_eqb tag (Z_to_bv 8 0) then Some (halt argument mask result) else None
  | [tag] => if bv_eqb tag (Z_to_bv 8 1) then Some decline else None
  | _ => None
  end.

Theorem deserialize_serialize : forall c, deserialize (serialize c) = Some c.
Proof. intros []; reflexivity. Qed.

Theorem serialize_injective : forall a b, serialize a = serialize b -> a = b.
Proof.
  intros a b H.
  apply (f_equal deserialize) in H.
  rewrite !deserialize_serialize in H. inversion H. reflexivity.
Qed.

Definition denote (c : Clause) : Sys SyscallEffect :=
  match c with
  | halt argument mask result => fun i =>
      (set_halted (bv_and (in_arg i (Z.to_nat (bv_unsigned argument)))
                         (Z_to_bv 64 (bv_unsigned mask))) ;;
      ret_only (Z_to_bv 64 (bv_unsigned result))) i
  | decline => unmodeled
  end.

(** Keep the full post-model and every effect ledger. [with_halted] acts on
    each development's actual Model; its extra state fields remain an audited
    cross-prover obligation. *)
Definition evaluate (c : Clause) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match c with
  | halt argument mask result =>
      Ok (mkEffect (Z_to_bv 64 (bv_unsigned result)) [] [])
        (with_halted (bv_and (in_arg i (Z.to_nat (bv_unsigned argument)))
                            (Z_to_bv 64 (bv_unsigned mask))) m) []
  | decline => Unmodeled
  end.

Theorem denote_normal_form : forall c i m o,
  denote c i m o <-> o = evaluate c i m.
Proof.
  intros [argument mask result|] i m [eff m' evs|];
    unfold denote, evaluate, bind, set_halted, modify, ret_only, pure, unmodeled, Sys_Monad;
    cbn.
  - split.
    + intros (x & m1 & evs1 & evs2 & H1 & H2 & Hevs).
      inversion H1; subst. inversion H2; subst. reflexivity.
    + intros H. inversion H; subst.
      eexists tt, _, [], []. repeat split; reflexivity.
  - split; intros H; [destruct H as [H|(x & m1 & evs & H1 & H2)]|];
      discriminate.
  - reflexivity.
  - reflexivity.
Qed.

Definition exit_clause : Clause := halt (Z_to_bv 8 0) (Z_to_bv 8 255) (Z_to_bv 8 0).

From LinuxProcessSemantics.LinuxProcessSem.Bridge Extra Dependency "exit.hex" as exit_artifact.
ReadFileString exit_artifact As artifact_text.

(** Read the entire file. Odd lengths or trailing tokens cannot silently
    disappear; hex_read_bytes is the existing image reader. *)
Definition read_artifact (text : PrimString.string) : option Clause :=
  let len := Z.to_nat (Uint63.to_Z (PrimString.length text)) in
  if Nat.eqb (len mod 2) 0 then
    match hex_read_bytes text 0 (len / 2) with
    | Some bs => deserialize bs
    | None => None
    end
  else None.

Definition artifact_clause : option Clause := read_artifact artifact_text.

Theorem artifact_checked : artifact_clause = Some exit_clause.
Proof. vm_compute. reflexivity. Qed.

Theorem artifact_unique : forall c, artifact_clause = Some c -> c = exit_clause.
Proof. intros c H. rewrite artifact_checked in H. congruence. Qed.

Theorem exit_spec_denotes : forall i m o,
  exit_spec (in_arg i 0) i m o <-> denote exit_clause i m o.
Proof. reflexivity. Qed.

Definition exit_number (no : word) : Prop :=
  bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.

Theorem exit_dispatch_denotes : forall i m o,
  exit_number (in_sysno i) ->
  syscall_spec i m o <-> denote exit_clause i m o.
Proof.
  intros i m o [Hno|Hno]; unfold syscall_spec, dispatch; rewrite Hno;
    apply exit_spec_denotes.
Qed.

(** Agreement with the file is proved, not assumed as a scoping premise. *)
Theorem exit_dispatch_artifact : forall i m o,
  exit_number (in_sysno i) ->
  (syscall_spec i m o <-> exists c, artifact_clause = Some c /\ denote c i m o).
Proof.
  intros i m o Hno. rewrite artifact_checked.
  rewrite (exit_dispatch_denotes i m o Hno).
  split.
  - intros H. exists exit_clause. auto.
  - intros (c & Hc & H). inversion Hc. subst. exact H.
Qed.

Theorem exit_dispatch_normal_form : forall i m o,
  exit_number (in_sysno i) ->
  (syscall_spec i m o <-> o = evaluate exit_clause i m).
Proof.
  intros i m o Hno. rewrite (exit_dispatch_denotes i m o Hno).
  apply denote_normal_form.
Qed.

(** Normalize the bitvector primitive to a common unsigned arithmetic formula,
    for every raw word rather than only the pilot's argument. *)
Theorem status_mod256 : forall code : word,
  bv_unsigned (bv_and code (Z_to_bv 64 255)) = (bv_unsigned code mod 256)%Z.
Proof.
  intros code. rewrite bv_and_unsigned.
  change (Z.land (bv_unsigned code) (Z.ones 8) = bv_unsigned code mod 2^8)%Z.
  apply Z.land_ones. lia.
Qed.

Theorem exit_dispatch_status : forall i m m' eff evs,
  exit_number (in_sysno i) -> syscall_spec i m (Ok eff m' evs) ->
  option_map bv_unsigned (m_halted m') = Some (bv_unsigned (in_arg i 0) mod 256)%Z.
Proof.
  intros i m m' eff evs Hno H.
  apply (proj1 (exit_dispatch_normal_form i m _ Hno)) in H.
  unfold evaluate, exit_clause in H. inversion H; subst.
  rewrite m_halted_with_halted. cbn. f_equal. apply status_mod256.
Qed.

Print Assumptions exit_dispatch_artifact.
Print Assumptions status_mod256.
Print Assumptions exit_dispatch_status.
