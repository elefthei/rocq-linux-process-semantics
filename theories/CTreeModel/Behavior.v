(** * CTreeModel.Behavior — the observables of a [Proc.ptree]

    The four fields of [Run.behavior], read off a choice tree through
    ctrees' transition relation [trans] alone, so they are invariant
    under [equ] and under strong bisimilarity ([ct_behavior_sbisim]).

    - [ct_traces]: the event lists along finite [trans] paths ([τ]
      steps are silent, [obs (Emit e)] steps contribute [e]);
    - [ct_errors] / [ct_unmodeled]: some path ends in a [val RFault] or
      [val RUnmodeled] transition (resp. [val RUnmodeled] only);
    - [ct_all_errors]: inductively, the tree has a transition and every
      transition is an error value or a non-value step to a tree that
      again satisfies [ct_all_errors].  Inductive, so a tree with an
      infinite path of [τ]/[obs] steps does not satisfy it, and a
      transition [val RHalt] or no transition at all refutes it — the
      same reading as [Run.all_traces_error].

    [ct_inf_trace] / [ct_diverges] are the infinite observables
    [Run.behavior] lacks: an infinite productive path, a silent divergence. *)

From Stdlib Require Import ZArith List Streams.
From Stdlib Require Eqdep.
From CTree Require Import CTree Eq.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State Run.
From LinuxProcessSemantics.CTreeModel Require Import Proc.
Import ListNotations CTree.
Set Universe Polymorphism.

Inductive ct_path : list event -> ptree result -> ptree result -> Prop :=
| ct_path_refl t t' : t ≅ t' -> ct_path [] t t'
| ct_path_tau tr t t' t'' :
    trans τ t t' -> ct_path tr t' t'' -> ct_path tr t t''
| ct_path_obs e tr t t' t'' :
    trans (obs (Emit e) tt) t t' -> ct_path tr t' t'' -> ct_path (e :: tr) t t''.

Definition ct_traces (t : ptree result) (tr : list event) : Prop :=
  exists t', ct_path tr t t'.

Definition ct_reaches (t : ptree result) (r : result) : Prop :=
  exists tr t' u, ct_path tr t t' /\ trans (val r) t' u.

Definition ct_errors (t : ptree result) : Prop :=
  ct_reaches t RFault \/ ct_reaches t RUnmodeled.

Definition ct_unmodeled (t : ptree result) : Prop := ct_reaches t RUnmodeled.

(** The label condition and the recursion are separate premises (rather
    than one disjunction) so that the induction principle carries the
    induction hypothesis. *)
Inductive ct_all_errors : ptree result -> Prop :=
| ct_all_errors_intro t :
    (exists l t', trans l t t') ->
    (forall l t', trans l t t' ->
       l = val RFault \/ l = val RUnmodeled \/ ~ is_val l) ->
    (forall l t', trans l t t' -> ~ is_val l -> ct_all_errors t') ->
    ct_all_errors t.

Definition ct_behavior (t : ptree result) : behavior :=
  {| bh_traces := ct_traces t;
     bh_errors := ct_errors t;
     bh_all_errors := ct_all_errors t;
     bh_unmodeled := ct_unmodeled t |}.

(** The behavior of the tree of [Run.run img lim en inp]. *)
Definition ct_run (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput)
    : behavior :=
  ct_behavior (proc_run img lim en inp).

(* =========================================================================
   Labels
   ========================================================================= *)

Lemma val_inj (x y : result) : @val procE result x = @val procE result y -> x = y.
Proof.
  intros H. inversion H. now apply Eqdep.EqdepTheory.inj_pair2 in H1.
Qed.

Lemma obs_emit_inj (e1 e2 : event) :
  @obs procE unit (Emit e1) tt = obs (Emit e2) tt -> e1 = e2.
Proof.
  intros H. now inversion H.
Qed.

(* =========================================================================
   Invariance under [equ]
   ========================================================================= *)

Lemma ct_path_equ tr t t' u u' :
  ct_path tr t t' -> t ≅ u -> t' ≅ u' -> ct_path tr u u'.
Proof.
  intros H; revert u u'.
  induction H as [t t' EQ | tr t t1 t' TR H IH | e tr t t1 t' TR H IH];
    intros u u' EQu EQu'.
  - constructor. now rewrite <- EQu, <- EQu'.
  - apply ct_path_tau with t1; [now rewrite <- EQu | now apply IH].
  - apply ct_path_obs with t1; [now rewrite <- EQu | now apply IH].
Qed.

#[global] Instance ct_path_equ_Proper tr :
  Proper (equ eq ==> equ eq ==> iff) (ct_path tr).
Proof.
  intros t u EQ t' u' EQ'; split; intros H.
  - exact (ct_path_equ _ _ _ _ _ H EQ EQ').
  - exact (ct_path_equ _ _ _ _ _ H (symmetry EQ) (symmetry EQ')).
Qed.

Lemma ct_all_errors_equ t u : ct_all_errors t -> t ≅ u -> ct_all_errors u.
Proof.
  intros H; revert u.
  induction H as [t Hex Hlab Hrec IH]; intros u EQ.
  constructor.
  - destruct Hex as (l & t' & TR). exists l, t'. now rewrite <- EQ.
  - intros l t' TR. apply (Hlab l t'). now rewrite EQ.
  - intros l t' TR Hnv. apply (IH l t'); [now rewrite EQ | exact Hnv | reflexivity].
Qed.

#[global] Instance ct_all_errors_equ_Proper :
  Proper (equ eq ==> iff) ct_all_errors.
Proof.
  intros t u EQ; split; intros H.
  - exact (ct_all_errors_equ _ _ H EQ).
  - exact (ct_all_errors_equ _ _ H (symmetry EQ)).
Qed.

(* =========================================================================
   Paths
   ========================================================================= *)

Lemma ct_path_app tr1 tr2 t t' t'' :
  ct_path tr1 t t' -> ct_path tr2 t' t'' -> ct_path (tr1 ++ tr2) t t''.
Proof.
  intros H; revert tr2 t''.
  induction H as [t t' EQ | tr t t1 t' TR H IH | e tr t t1 t' TR H IH];
    intros tr2 t'' H2; cbn.
  - now rewrite EQ.
  - eapply ct_path_tau; eauto.
  - eapply ct_path_obs; eauto.
Qed.

Lemma ct_path_prefix tr t t' p :
  ct_path tr t t' -> is_prefix p tr -> exists t'', ct_path p t t''.
Proof.
  intros H; revert p.
  induction H as [t t' EQ | tr t t1 t' TR H IH | e tr t t1 t' TR H IH];
    intros p Hp.
  - destruct p; [|contradiction]. exists t. now constructor.
  - destruct (IH p Hp) as (t'' & H'). exists t''. eapply ct_path_tau; eauto.
  - destruct p as [|x p].
    + exists t. now constructor.
    + destruct Hp as [-> Hp]. destruct (IH p Hp) as (t'' & H').
      exists t''. eapply ct_path_obs; eauto.
Qed.

Lemma ct_path_emit (u : ptree result) evs : ct_path evs (emit_evs evs u) u.
Proof.
  induction evs as [|e evs IH].
  - now constructor.
  - apply ct_path_obs with (emit_evs evs u); [|exact IH].
    apply trans_emit_cons. split; reflexivity.
Qed.

(* =========================================================================
   [ct_all_errors] through a tree with a single non-value transition
   ========================================================================= *)

Lemma ct_all_errors_inv t : ct_all_errors t ->
  (exists l t', trans l t t')
  /\ (forall l t', trans l t t' -> l = val RFault \/ l = val RUnmodeled \/ ~ is_val l)
  /\ (forall l t', trans l t t' -> ~ is_val l -> ct_all_errors t').
Proof. intros H. destruct H as [t Hex Hlab Hrec]. auto. Qed.

Lemma ct_all_errors_single t l0 t0 :
  ~ is_val l0 ->
  (forall l t', trans l t t' <-> l = l0 /\ t' ≅ t0) ->
  (ct_all_errors t <-> ct_all_errors t0).
Proof.
  intros Hnv Ht; split.
  - intros H. apply ct_all_errors_inv in H as (_ & _ & Hrec).
    apply (Hrec l0 t0); [apply Ht; split; reflexivity | exact Hnv].
  - intros H. constructor.
    + exists l0, t0. apply Ht. split; reflexivity.
    + intros l t' TR. apply Ht in TR as [-> _]. now right; right.
    + intros l t' TR _. apply Ht in TR as [_ EQ]. now rewrite EQ.
Qed.

Lemma ct_all_errors_emit_step pend (u : ptree result) :
  ct_all_errors (emit_evs pend (Step u)) <-> ct_all_errors u.
Proof.
  induction pend as [|e pend IH]; cbn [emit_evs].
  - apply (ct_all_errors_single _ τ u); [apply is_val_τ|].
    intros l t'. apply trans_step_iff.
  - rewrite <- IH.
    apply (ct_all_errors_single _ (obs (Emit e) tt) (emit_evs pend (Step u)));
      [apply is_val_obs|].
    intros l t'. apply (trans_emit_cons e pend (Step u)).
Qed.

(** Sanity: an error value satisfies the must-error predicate; a halt
    and a deadlock do not. *)
Example ct_all_errors_fault : ct_all_errors (Ret RFault).
Proof.
  constructor.
  - exists (val RFault), Stuck. apply trans_ret.
  - intros l t' TR. apply trans_ret_inv in TR as [_ ->]. now left.
  - intros l t' TR Hnv. apply trans_ret_inv in TR as [_ ->].
    exfalso. apply Hnv. constructor.
Qed.

Example ct_all_errors_not_halt : ~ ct_all_errors (Ret RHalt).
Proof.
  intros H. apply ct_all_errors_inv in H as (_ & Hlab & _).
  destruct (Hlab _ _ (trans_ret RHalt)) as [Hl | [Hl | Hl]].
  - apply val_inj in Hl. discriminate.
  - apply val_inj in Hl. discriminate.
  - apply Hl. constructor.
Qed.

Example ct_all_errors_not_stuck : ~ ct_all_errors (Stuck : ptree result).
Proof.
  intros H. apply ct_all_errors_inv in H as ((l & t' & TR) & _ & _).
  exact (trans_stuck_inv TR).
Qed.

(* =========================================================================
   Invariance under strong bisimilarity
   ========================================================================= *)

Lemma sbisim_trans_l (t u : ptree result) l t' :
  sbisim eq t u -> trans l t t' -> exists u', trans l u u' /\ sbisim eq t' u'.
Proof.
  intros EQ TR. step in EQ. destruct EQ as [F _].
  apply F in TR as (l' & u' & TR' & EQ' & <-). eauto.
Qed.

Lemma ct_path_sbisim tr t t' u :
  ct_path tr t t' -> sbisim eq t u -> exists u', ct_path tr u u' /\ sbisim eq t' u'.
Proof.
  intros H; revert u.
  induction H as [t t' EQ | tr t t1 t' TR H IH | e tr t t1 t' TR H IH];
    intros u EQu.
  - exists u. split; [now constructor | now rewrite <- EQ].
  - destruct (sbisim_trans_l _ _ _ _ EQu TR) as (u1 & TRu & EQ1).
    destruct (IH u1 EQ1) as (u' & Hu & EQ'). exists u'.
    split; [eapply ct_path_tau; eauto | exact EQ'].
  - destruct (sbisim_trans_l _ _ _ _ EQu TR) as (u1 & TRu & EQ1).
    destruct (IH u1 EQ1) as (u' & Hu & EQ'). exists u'.
    split; [eapply ct_path_obs; eauto | exact EQ'].
Qed.

Lemma ct_reaches_sbisim t u r :
  sbisim eq t u -> ct_reaches t r -> ct_reaches u r.
Proof.
  intros EQ (tr & t' & v & H & TR).
  destruct (ct_path_sbisim _ _ _ _ H EQ) as (u' & Hu & EQ').
  destruct (sbisim_trans_l _ _ _ _ EQ' TR) as (v' & TR' & _).
  now exists tr, u', v'.
Qed.

Lemma ct_all_errors_sbisim t u :
  ct_all_errors t -> sbisim eq t u -> ct_all_errors u.
Proof.
  intros H; revert u.
  induction H as [t Hex Hlab Hrec IH]; intros u EQ.
  assert (EQs : sbisim eq u t) by (symmetry; exact EQ).
  constructor.
  - destruct Hex as (l & t' & TR).
    destruct (sbisim_trans_l _ _ _ _ EQ TR) as (u' & TR' & _). eauto.
  - intros l u' TR.
    destruct (sbisim_trans_l _ _ _ _ EQs TR) as (t' & TR' & _).
    exact (Hlab _ _ TR').
  - intros l u' TR Hnv.
    destruct (sbisim_trans_l _ _ _ _ EQs TR) as (t' & TR' & EQ').
    apply (IH l t' TR' Hnv). symmetry. exact EQ'.
Qed.

Lemma ct_behavior_sbisim : forall t u, sbisim eq t u ->
  behavior_equiv (ct_behavior t) (ct_behavior u).
Proof.
  unfold behavior_equiv, ct_behavior; cbn.
  intros t u EQ.
  assert (EQs : sbisim eq u t) by (symmetry; exact EQ).
  unfold ct_traces, ct_errors, ct_unmodeled.
  split; [|split; [|split]].
  - intros tr; split; intros (t' & H).
    + destruct (ct_path_sbisim _ _ _ _ H EQ) as (u' & Hu & _). eauto.
    + destruct (ct_path_sbisim _ _ _ _ H EQs) as (u' & Hu & _). eauto.
  - split; intros [H | H];
      [left | right | left | right]; eapply ct_reaches_sbisim; eauto.
  - split; intros H; eapply ct_all_errors_sbisim; eauto.
  - split; intros H; eapply ct_reaches_sbisim; eauto.
Qed.

(** An infinite, productive trace: each event after finitely many [τ]s. *)
CoInductive ct_inf_trace : ptree result -> Stream event -> Prop :=
| ct_inf_trace_intro e s t u :
    ct_path [e] t u -> ct_inf_trace u s -> ct_inf_trace t (Cons e s).

(** An infinite path of [τ] steps. *)
CoInductive ct_diverges : ptree result -> Prop :=
| ct_diverges_intro t u : trans τ t u -> ct_diverges u -> ct_diverges t.

(** The first [n] elements of a stream. *)
Fixpoint stream_prefix {A} (n : nat) (s : Stream A) : list A :=
  match n with
  | O => []
  | S n => hd s :: stream_prefix n (tl s)
  end.

(** The refinement: the finite-prefix set [T] admits the infinite trace
    [s] when it contains every finite prefix of [s]. *)
Definition inf_refines (T : list event -> Prop) (s : Stream event) : Prop :=
  forall n, T (stream_prefix n s).
