(** * CTreeModel.InfWitness — what [ct_behavior] forgets

    Formal witnesses that [Behavior.ct_behavior] (= [Run.behavior] via
    [RunRefine.ct_run_refines_run]) projects away infinite behavior that a
    [ptree] carries: a silently diverging tree ([spin]) and a deadlocked
    one ([Stuck]) have the same behavior, and a tree can emit an infinite
    stream ([yes]) that no finite trace records. *)

From Stdlib Require Import List Streams.
From CTree Require Import CTree Eq.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run.
From LinuxProcessSemantics.CTreeModel Require Import Proc Behavior.
Import ListNotations CTree.
Set Universe Polymorphism.

(** A silent infinite loop: the tree of an instruction that jumps to
    itself. *)
Definition spin : ptree result := CTree.iterS (fun u : unit => Ret (inl u)) tt.

Lemma spin_unfold : spin ≅ Step spin.
Proof.
  unfold spin at 1. rewrite unfold_iterS. cbn [Monad.bind ctree_Monad].
  now rewrite bind_ret_l.
Qed.

(** [spin]'s only transition is a [τ] back to itself. *)
Lemma trans_spin l t' : trans l spin t' <-> l = τ /\ t' ≅ spin.
Proof. rewrite spin_unfold at 1. apply trans_step_iff. Qed.

(** [spin] diverges. *)
Lemma spin_diverges : ct_diverges spin.
Proof.
  cofix CIH. apply ct_diverges_intro with spin; [|exact CIH].
  apply trans_spin. split; reflexivity.
Qed.

(** [Stuck] has no transition, so does not diverge. *)
Lemma stuck_not_diverges : ~ ct_diverges (Stuck : ptree result).
Proof. inversion 1 as [t u TR]. exact (trans_stuck_inv TR). Qed.

(** Every path from [spin] is silent and returns to [spin]. *)
Lemma ct_path_spin tr t t' : ct_path tr t t' -> t ≅ spin -> tr = [] /\ t' ≅ spin.
Proof.
  induction 1 as [t t' EQ' | tr t t1 t' TR H IH | e tr t t1 t' TR H IH];
    intros EQ.
  - split; [reflexivity | now rewrite <- EQ'].
  - rewrite EQ in TR. apply trans_spin in TR as [_ EQ1]. exact (IH EQ1).
  - rewrite EQ in TR. apply trans_spin in TR as [Hl _]. discriminate.
Qed.

(** Every path from [Stuck] is empty. *)
Lemma ct_path_stuck tr t t' : ct_path tr t t' -> t ≅ Stuck -> tr = [] /\ t' ≅ Stuck.
Proof.
  destruct 1 as [t t' EQ' | tr t t1 t' TR _ | e tr t t1 t' TR _]; intros EQ.
  - split; [reflexivity | now rewrite <- EQ'].
  - rewrite EQ in TR. destruct (trans_stuck_inv TR).
  - rewrite EQ in TR. destruct (trans_stuck_inv TR).
Qed.

(** Neither tree reaches a value. *)
Lemma spin_not_reaches r : ~ ct_reaches spin r.
Proof.
  intros (tr & t' & u & H & TR).
  apply ct_path_spin in H as [_ EQ]; [|reflexivity].
  rewrite EQ in TR. apply trans_spin in TR as [Hl _]. discriminate.
Qed.

Lemma stuck_not_reaches r : ~ ct_reaches Stuck r.
Proof.
  intros (tr & t' & u & H & TR).
  apply ct_path_stuck in H as [_ EQ]; [|reflexivity].
  rewrite EQ in TR. exact (trans_stuck_inv TR).
Qed.

(** [spin] is not must-error: its [τ] recursion never bottoms out. *)
Lemma spin_not_all_errors : ~ ct_all_errors spin.
Proof.
  enough (G : forall t, ct_all_errors t -> t ≅ spin -> False)
    by (intros H; exact (G _ H (reflexivity _))).
  induction 1 as [t _ _ _ IH]; intros EQ.
  apply (IH τ spin); [|apply is_val_τ|reflexivity].
  rewrite EQ. apply trans_spin. split; reflexivity.
Qed.

(** Divergence and deadlock have the same [ct_behavior]. *)
Theorem spin_stuck_same_behavior :
  behavior_equiv (ct_behavior spin) (ct_behavior Stuck).
Proof.
  unfold behavior_equiv, ct_behavior, ct_traces, ct_errors, ct_unmodeled; cbn.
  split; [|split; [|split]].
  - intros tr; split; intros (t' & H).
    + apply ct_path_spin in H as [-> _]; [|reflexivity].
      exists Stuck. now constructor.
    + apply ct_path_stuck in H as [-> _]; [|reflexivity].
      exists spin. now constructor.
  - split; intros [H | H]; exfalso;
      [eapply spin_not_reaches | eapply spin_not_reaches
      | eapply stuck_not_reaches | eapply stuck_not_reaches]; exact H.
  - split; intros H; exfalso;
      [exact (spin_not_all_errors H) | exact (ct_all_errors_not_stuck H)].
  - split; intros H; exfalso;
      [exact (spin_not_reaches _ H) | exact (stuck_not_reaches _ H)].
Qed.

(** Hence divergence is not a function of [ct_behavior] (nor, via
    [RunRefine.ct_run_refines_run], of [Run.behavior]). *)
Theorem diverges_not_determined_by_behavior :
  exists t u : ptree result,
    behavior_equiv (ct_behavior t) (ct_behavior u) /\ ct_diverges t /\ ~ ct_diverges u.
Proof.
  exists spin, Stuck.
  split; [exact spin_stuck_same_behavior | split; [exact spin_diverges | exact stuck_not_diverges]].
Qed.

(** Emits [e] forever: an infinite trace, of which [ct_traces] keeps
    only the finite prefixes. *)
Definition yes (e : event) : ptree result :=
  CTree.iterS (fun u : unit => Vis (Emit e) (fun _ => Ret (inl u))) tt.

Lemma yes_unfold e : yes e ≅ Vis (Emit e) (fun _ => Step (yes e)).
Proof.
  unfold yes at 1. rewrite unfold_iterS. cbn [Monad.bind ctree_Monad].
  rewrite bind_vis.
  step. constructor. intros _. now rewrite bind_ret_l.
Qed.

Lemma yes_inf_trace e : ct_inf_trace (yes e) (Streams.const e).
Proof.
  cofix CIH. rewrite (unfold_Stream (Streams.const e)); cbn.
  apply ct_inf_trace_intro with (yes e); [|exact CIH].
  rewrite yes_unfold at 1.
  apply ct_path_obs with (Step (yes e)); [apply (trans_vis (Emit e) tt)|].
  apply ct_path_tau with (yes e); [apply trans_step | now constructor].
Qed.
