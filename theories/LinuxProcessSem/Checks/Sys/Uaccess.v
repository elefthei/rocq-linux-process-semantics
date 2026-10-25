(** * LinuxProcessSem.Checks.Sys.Uaccess — the user-buffer boundary checkers, and their proofs

    Mirrors [Sys/Uaccess.v], the spec side of the same boundary.

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

Definition check_access_ok_zero (buf count : word)
    (eff : SyscallEffect) (m : Model) (k : check_result) : check_result :=
  if access_okb buf (bv_unsigned count) then k
  else check_ret_only eff (errno_ret EFAULT) m [].

Definition check_efault_or (fallback : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if eff_is_errno EFAULT eff then CheckOk m []
  else check_ret_only eff fallback m [].

(** The two cases of [check_access_ok_zero] and [Uaccess.access_ok_zero]
    at once: they make the same test, so one split serves the hypothesis
    and the goal.  Leaves the arm's own answer first and the -EFAULT the
    range verdict forces second. *)
Ltac ok_zero_cases H b c :=
  unfold check_access_ok_zero in H; unfold access_ok_zero;
  destruct (access_okb b (bv_unsigned c)) eqn:Hok;
  cbv beta iota zeta in H |- *.

(** The same split for the completeness direction, where the guard is a
    hypothesis about the spec rather than about the checker. *)
Ltac ok_zero_split b c :=
  unfold access_ok_zero, check_access_ok_zero in *;
  destruct (access_okb b (bv_unsigned c));
  sys_unfold; cbv beta iota zeta in *; inv_ok.

Ltac ok_zero_complete b c := ok_zero_split b c; reflexivity.

Lemma check_efault_or_sound_ok : forall fallback i eff m m' evs,
  check_efault_or fallback eff m = CheckOk m' evs ->
  alt (err_ret EFAULT) (ret_only fallback) i m (Ok eff m' evs).
Proof.
  intros fallback i eff m m' evs H. unfold check_efault_or in H.
  destruct (eff_is_errno EFAULT eff) eqn:Hf.
  - apply eff_is_errno_true in Hf; subst eff. inversion H; subst.
    apply alt_l. apply pure_ok.
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply alt_r. apply pure_ok.
Qed.

Lemma check_efault_or_no_unmodeled : forall fallback eff m,
  check_efault_or fallback eff m <> CheckUnmodeled.
Proof.
  intros fallback eff m. unfold check_efault_or.
  destruct (eff_is_errno EFAULT eff); [discriminate|].
  apply check_ret_only_no_unmodeled.
Qed.

Lemma check_efault_or_complete_ok : forall fallback i eff m m' evs,
  alt (err_ret EFAULT) (ret_only fallback) i m (Ok eff m' evs) ->
  check_efault_or fallback eff m = CheckOk m' evs.
Proof.
  intros fallback i eff m m' evs H. unfold check_efault_or.
  destruct H as [Hf|Hz].
  - unfold err_ret, ret_only, pure, Sys_Monad in Hf. inv_ok.
    cbn. rewrite bv_eqb_refl. reflexivity.
  - unfold ret_only, pure, Sys_Monad in Hz. inv_ok.
    (* a fallback that also reads as [-EFAULT] is accepted by the first arm *)
    destruct (eff_is_errno EFAULT (mkEffect fallback [] [])) eqn:Hf.
    + apply eff_is_errno_true in Hf. inversion Hf. reflexivity.
    + cbn. rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma efault_or_no_unmodeled : forall fallback i m,
  ~ alt (err_ret EFAULT) (ret_only fallback) i m Unmodeled.
Proof.
  intros fallback i m H.
  destruct H as [H|H]; cbv [err_ret ret_only pure] in H; discriminate.
Qed.

Lemma check_efault_or_not_einval : forall fallback m m' evs,
  bv_eqb (errno_ret EINVAL) fallback = false ->
  check_efault_or fallback (mkEffect (errno_ret EINVAL) [] []) m
    = CheckOk m' evs -> False.
Proof.
  intros fallback m m' evs Hne H. unfold check_efault_or in H.
  replace (eff_is_errno EFAULT (mkEffect (errno_ret EINVAL) [] [])) with false
    in H by (vm_compute; reflexivity).
  cbn in H. rewrite Hne in H. discriminate.
Qed.
