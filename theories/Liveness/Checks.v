(** * [AF] applied to real images of this repository.

    [rwx_source_image] is the single-RWX-segment source binary of the
    [rwx_flag_ns] example, the image its equivalence proof uses.  The loop
    is the modeled [jal x0, 0] self-jump of [Checks.Omni]: a regression for
    the machine semantics, not an ELF replay. *)
From Stdlib Require Import ZArith List.
From CTree Require Import CTree Eq.
From TICL Require Import CTree.Core Logic.Core.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Omni.
From LinuxProcessSemantics.CTreeModel Require Import Proc Behavior RunRefine.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From LinuxProcessSemantics.Common Require Import CatSim.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import
  rwx_flag_ns_defs rwx_flag_ns_source rwx_flag_ns_code SourceMemImage.
From LinuxProcessSemantics.Liveness Require Import AF.
Import ListNotations CTree TiclNotations.
Local Open Scope ticl_scope.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Definition rwx_source_image : Image :=
  mkImage SourceMemImage.Source.loaded_segments
          SourceMemImage.Source.init_pc SourceMemImage.Source.phdrs.
Abbreviation exit5 := (stdpp.bitvector.definitions.Z_to_bv 64 5).

(** Every valid entry and input, any memory budget: exit 5. *)
Theorem rwx_source_must_exit_five : forall lim en inp,
  valid_entry rwx_source_image en inp -> valid_input inp ->
  must_exit_with exit5 rwx_source_image lim en inp.
Proof.
  intros lim [sp brk mb rnd] inp Hen Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as (Hsp & _).
  destruct Hvalid as (Hva & Hve & _).
  destruct Hsp as (Hlo & Hhi & _).
  apply (cat_must_exit_with_te source_segs SourceMemImage_init_pc SourceMemImage_phdrs
           sp brk mb rnd lim inp [] exit5).
  - rewrite source_init_pc_val. apply source_wexit; assumption.
  - unfold bufs_modeled. constructor.
Qed.

Theorem rwx_source_af_halts : forall lim en inp,
  valid_entry rwx_source_image en inp -> valid_input inp ->
  <[ {proc_run rwx_source_image lim en inp}, Pure |= AF done halts ]>.
Proof.
  intros lim en inp Hen Hvalid.
  apply (must_exit_with_af exit5); [now apply rwx_source_must_exit_five | constructor].
Qed.

Theorem rwx_source_no_reachable_divergence lim :
  image_no_reachable_divergence rwx_source_image lim.
Proof. exact (must_exit_no_reachable_divergence exit5 _ lim (rwx_source_must_exit_five lim)). Qed.

(** The self-jump takes a silent step back to itself ... *)
Lemma loop_silent_step lim : sstep loop_segments (loop_c lim) [] (SNext (loop_c lim)).
Proof.
  apply sstep_next_iff. split; [reflexivity|]. left.
  split; [reflexivity|]. split; [reflexivity|].
  exists loop_ms, (loop_model lim). split; [reflexivity|].
  cbn [cfg_ms cfg_model loop_c].
  rewrite mi_account_step_no_lazy by reflexivity.
  rewrite (with_mem_eta loop_ms), loop_fix.
  reflexivity.
Qed.

(** ... so its tree diverges silently ... *)
Theorem loop_diverges lim : ct_diverges (proc loop_segments (loop_c lim)).
Proof.
  cofix CIH.
  apply ct_diverges_intro with (proc loop_segments (loop_c lim)); [|exact CIH].
  apply trans_proc_iff. left. exists (loop_c lim).
  split; [apply loop_silent_step | split; reflexivity].
Qed.

(** ... and no [AF done] holds of it. *)
Theorem loop_not_af lim (R : result -> World procE -> Prop) :
  ~ <[ {proc loop_segments (loop_c lim)}, Pure |= AF done R ]>.
Proof.
  intros H.
  exact (af_done_no_reachable_divergence R _ H [] _ (ct_path_refl _ _ (reflexivity _))
           (loop_diverges lim)).
Qed.
