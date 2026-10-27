(** * The process tree read in TICL.

    [Proc.ptree] is already a TICL model ([ctree procE procB]), so this
    file only connects [MustExit]'s universal exit to TICL's [AF], and
    [AF] to the absence of silent divergence on every reachable residual.
    A result-only [AF] says the run halts; which exit code it halts with
    stays the business of [MustExit.must_exit_with].  A blocked call is a
    silent self-loop of the tree ([RunRefine.trans_proc_iff]), so it counts
    as divergence here. *)
From Stdlib Require Import ZArith List.
From CTree Require Import CTree Eq.
From TICL Require Import
  CTree.Core CTree.Logic.Trans CTree.Logic.CanStep CTree.Logic.AX CTree.Logic.AF
  Logic.Core.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State Run.
From LinuxProcessSemantics.CTreeModel Require Import Proc Behavior RunRefine InfRefine.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
Import ListNotations CTree TiclNotations.
Local Open Scope ticl_scope.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Abbreviation halts := (fun (r : result) (_ : World procE) => r = RHalt).

(** The events of one machine step, then its [Step], end in [u]. *)
Lemma emit_step_af (u : ptree result) (R : result -> World procE -> Prop) :
  (forall w, not_done w -> <[ u, w |= AF done R ]>) ->
  forall evs w, not_done w -> <[ {emit_evs evs (Step u)}, w |= AF done R ]>.
Proof.
  intros Hu evs; induction evs as [|e evs IH]; intros w Hd; cbn [emit_evs].
  - cright; apply anr_step; split; [csplit; auto with ticl | now apply Hu].
  - cright; apply (anr_vis (Emit e) _ tt); split; [csplit; auto with ticl |].
    intros []; apply IH; constructor.
Qed.

(** A machine that must exit with [code] halts on every tree path. *)
Theorem must_exit_at_af : forall segs code c,
  must_exit_at segs code c -> forall w, not_done w ->
  <[ {proc segs c}, w |= AF done halts ]>.
Proof.
  intros segs code c H.
  induction H as [c Hh _ | c Hnone Hprog Hnoerr _ IH]; intros w Hd.
  - (* halted: the only transition returns [RHalt] *)
    cright; csplit; [csplit; auto with ticl | |].
    + destruct Hd as [| Y e v]; eexists Stuck, _;
        [apply KtransDone | apply KtransFinish];
        apply (proj2 (trans_proc_iff _ _ _ _)); right; right; right; right; left;
        (split; [congruence | split; reflexivity]).
    + intros t' w' TR.
      apply ktrans_trans in TR as (l & TRl & Hl).
      apply trans_proc_iff in TRl.
      destruct TRl as [(c' & SS & -> & _)
        | [(e & evs & c' & SS & -> & _)
        | [((Hn & _) & -> & _)
        | [((Hn & _) & -> & _)
        | [(_ & -> & _)
        | ((Hn & _) & -> & _)]]]]];
        try (apply sstep_not_halted in SS; congruence); try congruence.
      destruct Hl as [(Hl & _) | [(Y & e & x & Hl & _) | [(x & Hl & -> & _ & ->) | (Y & e & v & x & Hl & -> & _ & ->)]]];
        try discriminate Hl; apply val_inj in Hl; subst x; cleft; csplit; reflexivity.
  - (* running: every transition is a step to a successor that must exit *)
    cright; csplit; [csplit; auto with ticl | |].
    + destruct Hprog as (evs & st & SS); destruct st as [c'|].
      * destruct evs as [|e evs].
        -- exists (proc segs c'), w; apply KtransTau; [exact Hd|].
           apply trans_proc_iff; left; exists c'; repeat split; [exact SS | reflexivity].
        -- exists (emit_evs evs (Step (proc segs c'))), (Obs (Emit e) tt).
           apply KtransObs; [exact Hd|].
           apply trans_proc_iff; right; left; exists e, evs, c'; repeat split; [exact SS | reflexivity].
      * exfalso; exact (Hnoerr evs SS).
    + assert (Herr : ~ fault_at segs c /\ ~ unmodeled_at segs c).
      { split; intros Hf; apply (Hnoerr []), sstep_error_iff; auto. }
      intros t' w' TR.
      apply ktrans_trans in TR as (l & TRl & Hl).
      apply trans_proc_iff in TRl.
      destruct TRl as [(c' & SS & -> & E)
        | [(e & evs & c' & SS & -> & E)
        | [(Hf & -> & _)
        | [(Hu & -> & _)
        | [(Hh & -> & _)
        | (Hb & -> & _)]]]]].
      * destruct Hl as [(_ & _ & ->) | [(Y & e & x & Hl & _) | [(x & Hl & _) | (Y & e & v & x & Hl & _)]]];
          try discriminate Hl.
        rewrite E; exact (IH [] c' SS w Hd).
      * destruct Hl as [(Hl & _) | [(Y & e' & x & _ & _ & ->) | [(x & Hl & _) | (Y & e' & v & x & Hl & _)]]];
          try discriminate Hl.
        rewrite E; apply emit_step_af; [exact (IH _ c' SS) | constructor].
      * exfalso; exact (proj1 Herr Hf).
      * exfalso; apply (proj2 Herr), unmodeled_at_cases; now left.
      * exfalso; exact (Hh Hnone).
      * exfalso; apply (proj2 Herr), unmodeled_at_cases; now right.
Qed.

(** The run-level form, for every [execve] entry and input. *)
Theorem must_exit_with_af : forall code img lim en inp,
  must_exit_with code img lim en inp -> forall w, not_done w ->
  <[ {proc_run img lim en inp}, w |= AF done halts ]>.
Proof.
  intros code [segs pc ph] lim [sp brk0 mbase rnd] inp H w Hd.
  cbn [must_exit_with proc_run] in *. exact (must_exit_at_af _ _ _ H w Hd).
Qed.

(** [AF] survives every step from a not-done world. *)
Lemma af_ktrans {X} (R : X -> World procE -> Prop) (t t' : ptree X) w w' :
  <[ t, w |= AF done R ]> -> not_done w -> |t, w| ↦ |t', w'| ->
  <[ t', w' |= AF done R ]>.
Proof.
  intros H Hd TR. rewrite unfold_entailsR in H |- *.
  destruct H as [? ? Hq | ? ? (_ & _ & Hnext)].
  - rewrite unfold_entailsR in Hq. inversion Hq; subst; inversion Hd.
  - exact (Hnext t' w' TR).
Qed.

Lemma af_ct_path (R : result -> World procE -> Prop) :
  forall tr (t u : ptree result), ct_path tr t u ->
  forall w, not_done w -> <[ t, w |= AF done R ]> ->
  exists w', not_done w' /\ <[ u, w' |= AF done R ]>.
Proof.
  induction 1 as [t t' EQ | tr t t' t'' TR P IH | e tr t t' t'' TR P IH]; intros w Hd H.
  - exists w; split; [exact Hd | now rewrite <- EQ].
  - apply (IH w Hd). exact (af_ktrans _ _ _ _ _ H Hd (KtransTau _ _ _ Hd TR)).
  - apply (IH (Obs (Emit e) tt) (NotDoneObs _ _)).
    exact (af_ktrans _ _ _ _ _ H Hd (KtransObs _ _ _ _ _ Hd TR)).
Qed.

Lemma acc_no_diverges (p : ptree result * World procE) :
  Acc kripke_step p -> not_done (snd p) -> ~ ct_diverges (fst p).
Proof.
  induction 1 as [[u w] _ IH]; cbn [fst snd]; intros Hd D.
  destruct D as [u0 u' TR D'].
  exact (IH (u', w) (KtransTau _ _ _ Hd TR) Hd D').
Qed.

(** No residual reachable from [t] diverges silently. *)
Definition no_reachable_divergence (t : ptree result) : Prop :=
  forall tr u, ct_path tr t u -> ~ ct_diverges u.

(** The same, for every valid [execve] entry and input of [img] under the
    memory budget [lim]. *)
Definition image_no_reachable_divergence (img : Image) (lim : Z) : Prop :=
  forall en inp, valid_entry img en inp -> valid_input inp ->
    no_reachable_divergence (proc_run img lim en inp).

(** [AF done] from the start excludes silent divergence after every
    reachable trace prefix. *)
Theorem af_done_no_reachable_divergence
    (R : result -> World procE -> Prop) (t : ptree result) :
  <[ t, Pure |= AF done R ]> -> no_reachable_divergence t.
Proof.
  intros H tr u P.
  destruct (af_ct_path R tr t u P Pure NotDonePure H) as (w & Hd & Hu).
  exact (acc_no_diverges (u, w) (af_done_accessible R u w Hu) Hd).
Qed.

(** An image that must exit on every valid start never diverges silently. *)
Theorem must_exit_no_reachable_divergence code img lim :
  (forall en inp, valid_entry img en inp -> valid_input inp ->
     must_exit_with code img lim en inp) ->
  image_no_reachable_divergence img lim.
Proof.
  intros H en inp Hen Hinp.
  exact (af_done_no_reachable_divergence _ _
           (must_exit_with_af code img lim en inp (H en inp Hen Hinp) Pure NotDonePure)).
Qed.
