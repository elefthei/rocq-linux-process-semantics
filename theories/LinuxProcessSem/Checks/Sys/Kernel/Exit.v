(** * LinuxProcessSem.Checks.Sys.Kernel.Exit — the exit (93), exit_group (94), wait4 (260) checkers, and their proofs

    Mirrors [Sys/Kernel/Exit.v], which answers to Linux [kernel/exit.c]:
    this file holds the checkers for the syscalls defined there, and no
    others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude.

Definition check_exit (code : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_ret_only eff (Z_to_bv 64 0)
    (with_halted (bv_and code (Z_to_bv 64 255)) m) [].

(** set_tid_address: no writes; the first call records a positive tid
    below the model's [PID_MAX_ENVELOPE] in [m_tid], and every later call
    must return the pinned value (see [Fork.set_tid_address_spec]). *)

Lemma check_exit_sound_ok : forall code eff m m' evs i,
  check_exit code eff m = CheckOk m' evs -> exit_spec code i m (Ok eff m' evs).
Proof.
  intros code eff m m' evs i H.
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  unfold exit_spec.
  eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_exit_sound_unmodeled : forall code eff m i,
  check_exit code eff m = CheckUnmodeled -> exit_spec code i m Unmodeled.
Proof.
  intros code eff m i H. now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_exit_complete_ok : forall code eff m m' evs i,
  exit_spec code i m (Ok eff m' evs) -> check_exit code eff m = CheckOk m' evs.
Proof.
  intros code eff m m' evs i H.
  unfold exit_spec in H. unfold check_exit. sys_unfold.
  cbv iota in H. inv_ok.
  cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma check_exit_complete_unmodeled : forall code m i eff,
  exit_spec code i m Unmodeled -> check_exit code eff m = CheckUnmodeled.
Proof.
  intros code m i eff H.
  unfold exit_spec in H. sys_unfold. cbv iota in H. inv_ok; discriminate.
Qed.

(* ------------------------------------------------- set_tid_address *)


(* ----------------------------------------------------------------- wait4 *)

(** wait4: three argument guards and one answer.  [Exit.wait4_spec] is
    a caller with no children, so -ECHILD is the whole of what a
    modeled call admits and every other kernel answer — a reaped pid,
    WNOHANG's bare 0, an -EFAULT through [stat_addr] — is REJECTED
    rather than accepted.  [stat_addr] is not read here for the same
    reason it is not read there: [kernel_wait4]'s copy-out is guarded
    on [ret > 0], so no -ECHILD touches it. *)
Definition check_wait4 (i : SyscallInput) (upid stat_addr options rusage : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (Z.eqb (bv_unsigned upid) WAIT_ANY32) then CheckUnmodeled
  else if negb (Z.eqb (bv_unsigned options) WNOHANG) then CheckUnmodeled
  else if negb (w_is0 rusage) then CheckUnmodeled
  else if m_has_children m then CheckUnmodeled
  else
    match eff with
    | mkEffectU r [] [] [] [] [] =>
        if bv_eqb r (errno_ret ECHILD) then CheckOk m [] else CheckReject
    | _ => CheckReject
    end.

(** Every effect field but the return must be empty: a -ECHILD moves no
    memory.  Five [destruct]s, one per ledger, each closing its cons
    case on the checker's catch-all. *)
Ltac wait4_empty_ledgers ws zs us cs ins tac :=
  destruct ws as [|? ?]; [|tac];
  destruct zs as [|? ?]; [|tac];
  destruct us as [|? ?]; [|tac];
  destruct cs as [|? ?]; [|tac];
  destruct ins as [|? ?]; [|tac].

Lemma check_wait4_sound_ok : forall i upid stat_addr options rusage eff m m' evs,
  check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs ->
  wait4_spec upid stat_addr options rusage i m (Ok eff m' evs).
Proof.
  intros i upid stat_addr options rusage [ret ws zs us cs ins] m m' evs H.
  unfold check_wait4 in H. unfold wait4_spec.
  destruct (negb (Z.eqb (bv_unsigned upid) WAIT_ANY32)); [discriminate|].
  destruct (negb (Z.eqb (bv_unsigned options) WNOHANG)); [discriminate|].
  destruct (negb (w_is0 rusage)); [discriminate|].
  destruct (m_has_children m) eqn:Hc; [discriminate|].
  wait4_empty_ledgers ws zs us cs ins discriminate.
  destruct (bv_eqb ret (errno_ret ECHILD)) eqn:Hr; [|discriminate].
  apply bv_eqb_eq in Hr. subst ret.
  inversion H; clear H; subst.
  eapply bind_ok0; [apply get_model_ok|].
  cbv beta. rewrite Hc. cbv iota.
  unfold err_ret, ret_only. apply pure_ok.
Qed.

Lemma check_wait4_sound_unmodeled :
  forall i upid stat_addr options rusage eff m,
  check_wait4 i upid stat_addr options rusage eff m = CheckUnmodeled ->
  wait4_spec upid stat_addr options rusage i m Unmodeled.
Proof.
  intros i upid stat_addr options rusage [ret ws zs us cs ins] m H.
  unfold check_wait4 in H. unfold wait4_spec.
  destruct (negb (Z.eqb (bv_unsigned upid) WAIT_ANY32)); [apply unmodeled_intro|].
  destruct (negb (Z.eqb (bv_unsigned options) WNOHANG)); [apply unmodeled_intro|].
  destruct (negb (w_is0 rusage)); [apply unmodeled_intro|].
  destruct (m_has_children m) eqn:Hc.
  { eapply bind_unmodeled2; [apply get_model_ok|].
    cbv beta. rewrite Hc. cbv iota. apply unmodeled_intro. }
  exfalso. wait4_empty_ledgers ws zs us cs ins discriminate.
  destruct (bv_eqb ret (errno_ret ECHILD)); discriminate.
Qed.

Lemma check_wait4_complete_ok :
  forall i upid stat_addr options rusage eff m m' evs,
  wait4_spec upid stat_addr options rusage i m (Ok eff m' evs) ->
  check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs.
Proof.
  intros i upid stat_addr options rusage eff m m' evs H.
  unfold wait4_spec in H. unfold check_wait4.
  destruct (negb (Z.eqb (bv_unsigned upid) WAIT_ANY32));
    [sys_unfold; inv_ok|].
  destruct (negb (Z.eqb (bv_unsigned options) WNOHANG)); [sys_unfold; inv_ok|].
  destruct (negb (w_is0 rusage)); [sys_unfold; inv_ok|].
  destruct (m_has_children m) eqn:Hc.
  { (* a caller with a child: the spec's continuation is [unmodeled],
       which admits no [Ok] at all *)
    destruct H as (x & m1 & evs1 & evs2 & Hg & Hk & _).
    unfold get_model in Hg. inversion Hg; subst.
    rewrite Hc in Hk. cbv iota in Hk. discriminate Hk. }
  destruct H as (x & m1 & evs1 & evs2 & Hg & Hk & He).
  unfold get_model in Hg. inversion Hg; subst.
  rewrite Hc in Hk. cbv iota in Hk.
  unfold err_ret, ret_only, pure, Sys_Monad in Hk. inversion Hk; subst.
  cbn. rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma check_wait4_complete_unmodeled :
  forall i upid stat_addr options rusage m eff,
  wait4_spec upid stat_addr options rusage i m Unmodeled ->
  check_wait4 i upid stat_addr options rusage eff m = CheckUnmodeled.
Proof.
  intros i upid stat_addr options rusage m eff H.
  unfold wait4_spec in H. unfold check_wait4.
  destruct (negb (Z.eqb (bv_unsigned upid) WAIT_ANY32)); [reflexivity|].
  destruct (negb (Z.eqb (bv_unsigned options) WNOHANG)); [reflexivity|].
  destruct (negb (w_is0 rusage)); [reflexivity|].
  destruct (m_has_children m) eqn:Hc; [reflexivity|].
  (* no children: the continuation is [err_ret ECHILD], which answers, so
     the spec cannot be [Unmodeled] here *)
  exfalso. destruct H as [Hg | (x & m1 & evs1 & Hg & Hk)].
  - unfold get_model in Hg. discriminate Hg.
  - unfold get_model in Hg. inversion Hg; subst.
    rewrite Hc in Hk. cbv iota in Hk.
    unfold err_ret, ret_only, pure, Sys_Monad in Hk. discriminate Hk.
Qed.
