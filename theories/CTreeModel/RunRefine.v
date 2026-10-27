(** * CTreeModel.RunRefine — the choice tree [Proc.proc] refines [Run.run]

    [ct_run_refines_run]: the traces of [Behavior.ct_run] and [Run.run]
    coincide, and each error fact of the tree ([bh_errors],
    [bh_all_errors], [bh_unmodeled]) is one of the run.  Not the
    converse: where the finite model declines a call whose shape
    [Block.would_block] recognizes as a wait, the tree takes a [τ] back to
    the same configuration ([blocked_tau]) and diverges
    ([blocked_diverges], [run_blocked_diverges]) instead of returning
    [RUnmodeled].  On runs that reach no such call ([block_free]) the two
    are equivalent ([block_free_iff], [run_ct_run_block_free]), and so
    [Equivalence.strong_universal_T] and its error-free variant hold of two
    images iff their [ct_*] restatements do, given block-freedom of every
    valid run ([strong_universal_iff], [strong_universal_error_free_iff]).

    The heart is [trans_proc_iff]: the transitions of [proc segs c] are
    in lockstep with [Run.sstep segs c] — a [τ] for a step without
    events, the first event as an [obs] for a step with events (the
    rest follow as [Vis] nodes, then the step's [τ]), a [val] for each
    error rule other than a blocked call and for a halted model, and a
    [τ] self-loop for a blocked call.  The [←] directions of the bridges
    walk a ctree path with the invariant [reach], which also covers trees
    in the middle of a step's events.

    [proc_fin_branching]: every [proc segs c] has finitely many
    transitions up to [equ], from [Finite.syscall_spec_finite]. *)

From Stdlib Require Import ZArith List.
From CTree Require Import CTree Eq.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Finite.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.CTreeModel Require Import Proc Behavior Block.
Import ListNotations CTree.
Set Universe Polymorphism.
(* As in [Proc]: keep [procE]'s answer universe generic so TICL's worlds apply. *)
Unset Universe Minimization ToSet.

Section WithSegs.

Variable segs : list Segment.

(* =========================================================================
   LTS-side inversions (no ctrees)
   ========================================================================= *)

(** The [SError] rules of [Run.sstep] other than the two
    [Run.unmodeled_at] ones. *)
Definition fault_at (c : config) : Prop :=
  m_halted (cfg_model c) = None /\
  ( (ms_svc_pending (cfg_ms c) = None
     /\ mi_account_step segs (cfg_ms c) (cfg_model c) = MachineFault)
  \/ (exists x8 eff model' evs, ms_svc_pending (cfg_ms c) = Some x8
      /\ syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c)
                      (Monad.Ok eff model' evs)
      /\ outcome_next (cfg_ms c) eff model' evs = None)).

(** A pending call the finite model declines and [Block.would_block]
    recognizes as a wait. *)
Definition blocked_at (c : config) : Prop :=
  m_halted (cfg_model c) = None /\
  exists x8, ms_svc_pending (cfg_ms c) = Some x8
    /\ syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) Monad.Unmodeled
    /\ would_block (sys_input segs (cfg_ms c) x8) (cfg_model c) = true.

(** [Run.unmodeled_at] minus the blocked shapes. *)
Definition declined_at (c : config) : Prop :=
  m_halted (cfg_model c) = None /\
  ( (ms_svc_pending (cfg_ms c) = None
     /\ mi_account_step segs (cfg_ms c) (cfg_model c) = MachineUnmodeled)
  \/ (exists x8, ms_svc_pending (cfg_ms c) = Some x8
      /\ syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) Monad.Unmodeled
      /\ would_block (sys_input segs (cfg_ms c) x8) (cfg_model c) = false)).

Lemma unmodeled_at_cases c : unmodeled_at segs c <-> declined_at c \/ blocked_at c.
Proof.
  unfold unmodeled_at, declined_at, blocked_at. split.
  - intros [Hh [Hi | (x8 & Hp & Hspec)]]; [left; auto|].
    destruct (would_block (sys_input segs (cfg_ms c) x8) (cfg_model c)) eqn:Hb.
    + right. eauto.
    + left. split; [exact Hh|]. right. eauto.
  - intros [(Hh & [Hi | (x8 & Hp & Hspec & _)]) | (Hh & x8 & Hp & Hspec & _)];
      split; eauto.
Qed.

Lemma sstep_not_halted c evs st :
  sstep segs c evs st -> m_halted (cfg_model c) = None.
Proof. intros H. destruct H; assumption. Qed.

Lemma sstep_error_iff c evs :
  sstep segs c evs SError <-> evs = [] /\ (fault_at c \/ unmodeled_at segs c).
Proof.
  unfold fault_at, unmodeled_at. split.
  - intros H. remember SError as st eqn:Est.
    destruct H as
      [ms model ms' model' Hh Hp Hs | ms model Hh Hp Hs | ms model Hh Hp Hs
      | ms model x8 eff model' model'' evs0 Hh Hp Hspec Hh' Hmat
      | ms model x8 eff model' evs0 Hh Hp Hspec Hh' Hmat
      | ms model x8 eff model' evs0 code Hh Hp Hspec Hh' Hk
      | ms model x8 eff model' evs0 sig Hh Hp Hspec Hk
      | ms model x8 Hh Hp Hspec]; try discriminate; cbn; split; auto.
    + left. split; [exact Hh|]. right. exists x8, eff, model', evs0.
      repeat split; auto. unfold outcome_next. now rewrite Hh', Hmat.
    + right. split; [exact Hh|]. right. eauto.
  - intros [-> [(Hh & [(Hp & Hs) | (x8 & eff & model' & evs0 & Hp & Hspec & Hon)])
              | (Hh & [(Hp & Hs) | (x8 & Hp & Hspec)])]];
      destruct c as [ms model]; cbn in *.
    + now apply sstep_instr_fault.
    + unfold outcome_next in Hon.
      destruct (m_halted model') as [code|] eqn:Hh'.
      * destruct (m_killed model'); discriminate.
      * destruct (materialize_model_accesses model' (syscall_effect_accesses eff))
          eqn:Hmat; [discriminate|].
        eapply sstep_syscall_materialization_fault; eauto.
    + now apply sstep_instr_unmodeled.
    + eapply sstep_syscall_unmodeled; eauto.
Qed.

Lemma sstep_next_iff c evs c' :
  sstep segs c evs (SNext c') <->
  m_halted (cfg_model c) = None /\
  ( (ms_svc_pending (cfg_ms c) = None /\ evs = []
     /\ exists ms' model', c' = mkCfg ms' model'
        /\ mi_account_step segs (cfg_ms c) (cfg_model c) = MachineOk (ms', model'))
  \/ (exists x8 eff model' evs0, ms_svc_pending (cfg_ms c) = Some x8
      /\ syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c)
                      (Monad.Ok eff model' evs0)
      /\ outcome_next (cfg_ms c) eff model' evs0 = Some (evs, c'))).
Proof.
  split.
  - intros H. remember (SNext c') as st eqn:Est.
    destruct H as
      [ms model ms' model' Hh Hp Hs | ms model Hh Hp Hs | ms model Hh Hp Hs
      | ms model x8 eff model' model'' evs0 Hh Hp Hspec Hh' Hmat
      | ms model x8 eff model' evs0 Hh Hp Hspec Hh' Hmat
      | ms model x8 eff model' evs0 code Hh Hp Hspec Hh' Hk
      | ms model x8 eff model' evs0 sig Hh Hp Hspec Hk
      | ms model x8 Hh Hp Hspec]; try discriminate;
      injection Est as <-; cbn; split; auto.
    + left. eauto 6.
    + right. exists x8, eff, model', evs0. repeat split; auto.
      unfold outcome_next. now rewrite Hh', Hmat.
    + right. exists x8, eff, model', evs0. repeat split; auto.
      unfold outcome_next. now rewrite Hh', Hk.
    + right. exists x8, eff, model', evs0. repeat split; auto.
      unfold outcome_next.
      destruct (m_halted model') as [code|] eqn:Hh'.
      * now rewrite Hk.
      * rewrite (m_killed_of_m_halted_none _ Hh') in Hk. discriminate.
  - intros [Hh [(Hp & -> & ms' & model' & -> & Hs)
              | (x8 & eff & model' & evs0 & Hp & Hspec & Hon)]];
      destruct c as [ms model]; cbn in *.
    + now apply sstep_instr.
    + unfold outcome_next in Hon.
      destruct (m_halted model') as [code|] eqn:Hh'.
      * destruct (m_killed model') as [sig|] eqn:Hk; injection Hon as <- <-.
        -- eapply sstep_killed; eauto.
        -- eapply sstep_exit; eauto.
      * destruct (materialize_model_accesses model' (syscall_effect_accesses eff))
          as [model''|] eqn:Hmat; [|discriminate].
        injection Hon as <- <-. eapply sstep_syscall; eauto.
Qed.

(* =========================================================================
   Lockstep
   ========================================================================= *)

Definition kont (lr : config + result) : ptree result :=
  match lr with inl c' => Step (proc segs c') | inr r => Ret r end.

Lemma emit_ret_kont evs c' :
  CTree.bind (emit_evs evs (Ret (inl c'))) kont ≅ emit_evs evs (Step (proc segs c')).
Proof.
  induction evs as [|e evs IH]; cbn [emit_evs].
  - now rewrite bind_ret_l.
  - rewrite bind_vis. step. constructor. intros _. apply IH.
Qed.

Lemma bind_br_choose ms model x8 o
    (Ho : syscall_spec (sys_input segs ms x8) model o) l t' :
  trans l (CTree.bind (outcome_tree (sys_input segs ms x8) ms model o) kont) t' ->
  trans l (CTree.bind (Br (Choose (sys_input segs ms x8) model)
                          (fun ox => outcome_tree (sys_input segs ms x8) ms model
                                       (proj1_sig ox))) kont) t'.
Proof.
  intros TR. rewrite bind_br.
  eapply trans_br with (x := exist _ o Ho); [exact TR | reflexivity].
Qed.

Definition proc_step (c : config) (l : @label procE) (t' : ptree result) : Prop :=
     (exists c', sstep segs c [] (SNext c') /\ l = τ /\ t' ≅ proc segs c')
  \/ (exists e evs c', sstep segs c (e :: evs) (SNext c') /\ l = obs (Emit e) tt
        /\ t' ≅ emit_evs evs (Step (proc segs c')))
  \/ (fault_at c /\ l = val RFault /\ t' ≅ Stuck)
  \/ (declined_at c /\ l = val RUnmodeled /\ t' ≅ Stuck)
  \/ (m_halted (cfg_model c) <> None /\ l = val RHalt /\ t' ≅ Stuck)
  \/ (blocked_at c /\ l = τ /\ t' ≅ proc segs c).

Lemma trans_proc_inv c l t' : trans l (proc segs c) t' -> proc_step c l t'.
Proof.
  unfold proc_step, fault_at, declined_at, blocked_at.
  intros TR. rewrite (proc_unfold segs c) in TR.
  cbn [Monad.bind ctree_Monad] in TR. fold kont in TR.
  destruct c as [ms model]. cbn [step_tree cfg_ms cfg_model] in *.
  destruct (m_halted model) as [code|] eqn:Hh.
  - rewrite bind_ret_l in TR. cbv beta iota delta [kont] in TR.
    apply trans_ret_inv in TR as [EQ ->].
    right; right; right; right; left. split; [discriminate | auto].
  - destruct (ms_svc_pending ms) as [x8|] eqn:Hp.
    + rewrite bind_br in TR. apply trans_br_inv in TR as [[o Ho] TR].
      cbn [proj1_sig] in TR.
      destruct o as [eff model' evs|]; cbn [outcome_tree] in TR.
      * destruct (outcome_next ms eff model' evs) as [[evs' c']|] eqn:Hon.
        -- rewrite emit_ret_kont in TR. destruct evs' as [|e evs'].
           ++ apply trans_step_iff in TR as [-> EQ].
              left. exists c'. repeat split; auto. apply sstep_next_iff. cbn.
              split; [exact Hh|]. right. exists x8, eff, model', evs. auto.
           ++ apply trans_emit_cons in TR as [-> EQ].
              right; left. exists e, evs', c'. repeat split; auto.
              apply sstep_next_iff. cbn.
              split; [exact Hh|]. right. exists x8, eff, model', evs. auto.
        -- rewrite bind_ret_l in TR. cbv beta iota delta [kont] in TR.
           apply trans_ret_inv in TR as [EQ ->].
           right; right; left. repeat split; auto.
           right. exists x8, eff, model', evs. auto.
      * destruct (would_block (sys_input segs ms x8) model) eqn:Hb;
          rewrite bind_ret_l in TR; cbv beta iota delta [kont] in TR.
        -- apply trans_step_iff in TR as [-> EQ].
           right; right; right; right; right. repeat split; auto. exists x8. auto.
        -- apply trans_ret_inv in TR as [EQ ->].
           right; right; right; left. repeat split; auto.
           right. exists x8. auto.
    + destruct (mi_account_step segs ms model) as [[ms' model']| |] eqn:Hs;
        rewrite bind_ret_l in TR; cbv beta iota delta [kont] in TR.
      * apply trans_step_iff in TR as [-> EQ].
        left. exists (mkCfg ms' model'). repeat split; auto.
        now apply sstep_instr.
      * apply trans_ret_inv in TR as [EQ ->].
        right; right; left. repeat split; auto.
      * apply trans_ret_inv in TR as [EQ ->].
        right; right; right; left. repeat split; auto.
Qed.

Lemma trans_proc_intro c l t' : proc_step c l t' -> trans l (proc segs c) t'.
Proof.
  unfold proc_step, fault_at, declined_at, blocked_at.
  intros [(c' & Hs & -> & EQ) | [(e & evs & c' & Hs & -> & EQ)
         | [(Hf & -> & EQ) | [(Hu & -> & EQ) | [(Hh & -> & EQ) | (Hb & -> & EQ)]]]]];
    rewrite (proc_unfold segs c), EQ; cbn [Monad.bind ctree_Monad]; fold kont.
  - apply sstep_next_iff in Hs as
        [Hh [(Hp & _ & ms' & model' & -> & Hs) | (x8 & eff & model' & evs0 & Hp & Hspec & Hon)]];
      destruct c as [ms model]; cbn [step_tree cfg_ms cfg_model] in *;
      rewrite Hh, Hp.
    + rewrite Hs, bind_ret_l. apply trans_step.
    + apply (bind_br_choose _ _ _ _ Hspec). cbn [outcome_tree].
      rewrite Hon, emit_ret_kont. apply trans_step.
  - apply sstep_next_iff in Hs as
        [Hh [(Hp & Habs & _) | (x8 & eff & model' & evs0 & Hp & Hspec & Hon)]];
      [discriminate|].
    destruct c as [ms model]; cbn [step_tree cfg_ms cfg_model] in *.
    rewrite Hh, Hp.
    apply (bind_br_choose _ _ _ _ Hspec). cbn [outcome_tree].
    rewrite Hon, emit_ret_kont. apply trans_emit_cons. split; reflexivity.
  - destruct c as [ms model]; cbn [step_tree cfg_ms cfg_model] in *.
    destruct Hf as (Hh & [(Hp & Hs) | (x8 & eff & model' & evs & Hp & Hspec & Hon)]);
      rewrite Hh, Hp.
    + rewrite Hs, bind_ret_l. apply trans_ret.
    + apply (bind_br_choose _ _ _ _ Hspec). cbn [outcome_tree].
      rewrite Hon, bind_ret_l. apply trans_ret.
  - destruct c as [ms model]; cbn [step_tree cfg_ms cfg_model] in *.
    destruct Hu as (Hh & [(Hp & Hs) | (x8 & Hp & Hspec & Hb)]); rewrite Hh, Hp.
    + rewrite Hs, bind_ret_l. apply trans_ret.
    + apply (bind_br_choose _ _ _ _ Hspec). cbn [outcome_tree].
      rewrite Hb, bind_ret_l. apply trans_ret.
  - destruct c as [ms model]; cbn [step_tree cfg_ms cfg_model] in *.
    destruct (m_halted model) as [code|]; [|congruence].
    rewrite bind_ret_l. apply trans_ret.
  - destruct c as [ms model]; cbn [step_tree cfg_ms cfg_model] in *.
    destruct Hb as (Hh & x8 & Hp & Hspec & Hb). rewrite Hh, Hp.
    apply (bind_br_choose _ _ _ _ Hspec). cbn [outcome_tree].
    rewrite Hb, bind_ret_l. apply trans_step.
Qed.

Lemma trans_proc_iff c l t' : trans l (proc segs c) t' <-> proc_step c l t'.
Proof. split; [apply trans_proc_inv | apply trans_proc_intro]. Qed.

(** A blocked call is a [τ] back to the same tree: the kernel's wait loop
    with nothing to wake it. *)
Lemma blocked_tau c : blocked_at c -> trans τ (proc segs c) (proc segs c).
Proof. intros Hb. apply trans_proc_intro. right; right; right; right; right. auto. Qed.

Lemma blocked_diverges c : blocked_at c -> ct_diverges (proc segs c).
Proof.
  intros Hb. cofix CIH.
  apply ct_diverges_intro with (proc segs c); [exact (blocked_tau c Hb) | exact CIH].
Qed.

Lemma sstep_path c evs c' :
  sstep segs c evs (SNext c') -> ct_path evs (proc segs c) (proc segs c').
Proof.
  intros Hs. destruct evs as [|e evs].
  - apply ct_path_tau with (proc segs c'); [|now constructor].
    apply trans_proc_intro. left. eauto.
  - apply ct_path_obs with (emit_evs evs (Step (proc segs c'))).
    + apply trans_proc_intro. right; left. exists e, evs, c'. auto.
    + rewrite <- (app_nil_r evs) at 1.
      eapply ct_path_app; [apply ct_path_emit|].
      apply ct_path_tau with (proc segs c'); [apply trans_step | now constructor].
Qed.

Lemma star_path c tr c' : star segs c tr c' -> ct_path tr (proc segs c) (proc segs c').
Proof.
  intros H. induction H as [c | c1 evs c2 tr c3 Hs H IH].
  - now constructor.
  - eapply ct_path_app; [apply sstep_path; exact Hs | exact IH].
Qed.

Lemma sstep_error_trans c evs : sstep segs c evs SError ->
  blocked_at c \/
  exists r, (r = RFault \/ r = RUnmodeled) /\ trans (val r) (proc segs c) Stuck.
Proof.
  intros H. apply sstep_error_iff in H as [_ [Hf | Hu]].
  - right. exists RFault. split; [now left|].
    apply trans_proc_intro. right; right; left. auto.
  - apply unmodeled_at_cases in Hu as [Hd | Hb]; [right | now left].
    exists RUnmodeled. split; [now right|].
    apply trans_proc_intro. right; right; right; left. auto.
Qed.

Lemma trans_val_proc c r u : trans (val r) (proc segs c) u ->
  (r = RFault /\ fault_at c) \/ (r = RUnmodeled /\ unmodeled_at segs c)
  \/ (r = RHalt /\ m_halted (cfg_model c) <> None).
Proof.
  intros TR. apply trans_proc_inv in TR as
    [(? & _ & Hl & _) | [(? & ? & ? & _ & Hl & _)
    | [(Hf & Hl & _) | [(Hu & Hl & _) | [(Hh & Hl & _) | (_ & Hl & _)]]]]];
    try discriminate; apply val_inj in Hl; subst; auto.
  right; left. split; [reflexivity|]. apply unmodeled_at_cases. now left.
Qed.

(* =========================================================================
   The invariant along a ctree path
   ========================================================================= *)

Inductive reach (c0 : config) : list event -> ptree result -> Prop :=
| reach_proc c tr t : star segs c0 tr c -> t ≅ proc segs c -> reach c0 tr t
| reach_mid c tr done pend c' t :
    star segs c0 tr c -> sstep segs c (done ++ pend) (SNext c') ->
    t ≅ emit_evs pend (Step (proc segs c')) -> reach c0 (tr ++ done) t.

Lemma reach_equ c0 d t u : reach c0 d t -> t ≅ u -> reach c0 d u.
Proof.
  intros [c tr t' Hst EQ | c tr done pend c' t' Hst Hs EQ] EQu.
  - apply reach_proc with c; [exact Hst | now rewrite <- EQu].
  - eapply reach_mid; [exact Hst | exact Hs | now rewrite <- EQu].
Qed.

Lemma reach_tau c0 d t t1 : reach c0 d t -> trans τ t t1 -> reach c0 d t1.
Proof.
  intros [c tr t' Hst EQ | c tr done pend c' t' Hst Hs EQ] TR; rewrite EQ in TR.
  - apply trans_proc_inv in TR as
      [(c' & Hs & _ & EQ1) | [(? & ? & ? & _ & Hl & _)
      | [(_ & Hl & _) | [(_ & Hl & _) | [(_ & Hl & _) | (_ & _ & EQ1)]]]]];
      try discriminate.
    + apply reach_proc with c'; [|exact EQ1].
      rewrite <- (app_nil_r tr). eapply star_trans; [exact Hst | now apply star_one].
    + apply reach_proc with c; [exact Hst | exact EQ1].
  - destruct pend as [|e pend].
    + apply trans_step_iff in TR as [_ EQ1].
      apply reach_proc with c'; [|exact EQ1].
      rewrite app_nil_r in Hs. eapply star_trans; [exact Hst | now apply star_one].
    + apply trans_emit_cons in TR as [Hl _]. discriminate.
Qed.

Lemma reach_obs c0 d t e t1 :
  reach c0 d t -> trans (obs (Emit e) tt) t t1 -> reach c0 (d ++ [e]) t1.
Proof.
  intros [c tr t' Hst EQ | c tr done pend c' t' Hst Hs EQ] TR; rewrite EQ in TR.
  - apply trans_proc_inv in TR as
      [(? & _ & Hl & _) | [(e' & evs & c' & Hs & Hl & EQ1)
      | [(_ & Hl & _) | [(_ & Hl & _) | [(_ & Hl & _) | (_ & Hl & _)]]]]];
      try discriminate.
    apply obs_emit_inj in Hl. subst e'.
    eapply reach_mid with (done := [e]); [exact Hst | exact Hs | exact EQ1].
  - destruct pend as [|e' pend].
    + apply trans_step_iff in TR as [Hl _]. discriminate.
    + apply trans_emit_cons in TR as [Hl EQ1]. apply obs_emit_inj in Hl. subst e'.
      rewrite <- app_assoc.
      eapply reach_mid with (done := done ++ [e]); [exact Hst | | exact EQ1].
      now rewrite <- app_assoc.
Qed.

Lemma reach_path tr t t' : ct_path tr t t' ->
  forall c0 d, reach c0 d t -> reach c0 (d ++ tr) t'.
Proof.
  induction 1 as [t t' EQ | tr t t1 t' TR H IH | e tr t t1 t' TR H IH];
    intros c0 d Hr.
  - rewrite app_nil_r. eapply reach_equ; eauto.
  - eapply IH, reach_tau; eauto.
  - replace (d ++ e :: tr) with ((d ++ [e]) ++ tr) by now rewrite <- app_assoc.
    eapply IH, reach_obs; eauto.
Qed.

Lemma reach_start c : reach c [] (proc segs c).
Proof. apply reach_proc with c; [apply star_refl | reflexivity]. Qed.

Lemma reach_val_inv c0 d t (r : result) u : reach c0 d t -> trans (val r) t u ->
  exists c, star segs c0 d c /\ t ≅ proc segs c.
Proof.
  intros [c tr t' Hst EQ | c tr done pend c' t' Hst Hs EQ] TR.
  - eauto.
  - rewrite EQ in TR. destruct pend as [|e pend].
    + apply trans_step_iff in TR as [Hl _]. discriminate.
    + apply trans_emit_cons in TR as [Hl _]. discriminate.
Qed.

(* =========================================================================
   The four bridges
   ========================================================================= *)

Lemma obs_trace_iff c tr : obs_trace segs c tr <-> ct_traces (proc segs c) tr.
Proof.
  split.
  - intros (tr' & c' & Hst & Hp).
    exact (ct_path_prefix _ _ _ _ (star_path _ _ _ Hst) Hp).
  - intros (t' & H).
    pose proof (reach_path _ _ _ H c [] (reach_start c)) as Hr. cbn in Hr.
    destruct Hr as [c1 tr t Hst _ | c1 tr0 done pend c2 t Hst Hs _].
    + exists tr, c1. split; [exact Hst | apply is_prefix_refl].
    + exists (tr0 ++ done ++ pend), c2. split.
      * eapply star_trans; [exact Hst | now apply star_one].
      * rewrite app_assoc. apply is_prefix_app.
Qed.

Lemma reaches_val c r : ct_reaches (proc segs c) r ->
  exists tr c1 u, star segs c tr c1 /\ trans (val r) (proc segs c1) u.
Proof.
  intros (tr & t' & u & H & TR).
  pose proof (reach_path _ _ _ H c [] (reach_start c)) as Hr. cbn in Hr.
  destruct (reach_val_inv _ _ _ _ _ Hr TR) as (c1 & Hst & EQ).
  rewrite EQ in TR. eauto.
Qed.

Lemma ct_errors_reaches_error c : ct_errors (proc segs c) -> reaches_error segs c.
Proof.
  intros [H | H]; apply reaches_val in H as (tr & c1 & u & Hst & TR);
    apply trans_val_proc in TR as [(Hr & Hf) | [(Hr & Hu) | (Hr & _)]];
    try discriminate;
    exists tr, c1, []; split; auto; apply sstep_error_iff; auto.
Qed.

Lemma ct_unmodeled_reaches_unmodeled c :
  ct_unmodeled (proc segs c) -> reaches_unmodeled segs c.
Proof.
  intros H. apply reaches_val in H as (tr & c1 & u & Hst & TR).
  apply trans_val_proc in TR as [(Hr & _) | [(_ & Hu) | (Hr & _)]];
    try discriminate.
  exists tr, c1. auto.
Qed.

(** An error of the run is one of the tree, or the run reaches a blocked
    call (where the tree diverges instead). *)
Lemma reaches_error_ct c : reaches_error segs c ->
  ct_errors (proc segs c) \/ exists tr c1, star segs c tr c1 /\ blocked_at c1.
Proof.
  intros (tr & c1 & evs & Hst & Hs).
  destruct (sstep_error_trans _ _ Hs) as [Hb | (r & [-> | ->] & TR)]; [right; eauto | |];
    left; [left | right]; exists tr, (proc segs c1), Stuck;
    split; auto; apply star_path, Hst.
Qed.

Lemma reaches_unmodeled_ct c : reaches_unmodeled segs c ->
  ct_unmodeled (proc segs c) \/ exists tr c1, star segs c tr c1 /\ blocked_at c1.
Proof.
  intros (tr & c1 & Hst & Hu).
  apply unmodeled_at_cases in Hu as [Hd | Hb]; [left | right; eauto].
  exists tr, (proc segs c1), Stuck. split; [apply star_path, Hst|].
  apply trans_proc_intro. right; right; right; left. auto.
Qed.

Lemma ct_all_traces_error t : ct_all_errors t ->
  (forall c, t ≅ proc segs c -> all_traces_error segs c)
  /\ (forall pend c', t ≅ emit_evs pend (Step (proc segs c')) ->
                     all_traces_error segs c').
Proof.
  induction 1 as [t Hex Hlab Hrec IH]. split.
  - intros c EQ. constructor.
    + destruct Hex as (l & t' & TR0).
      pose proof TR0 as TR. rewrite EQ in TR.
      apply trans_proc_inv in TR as
        [(c' & Hs & _) | [(e & evs & c' & Hs & _)
        | [(Hf & _) | [(Hu & _) | [(_ & -> & _) | (Hb & _)]]]]].
      * eauto.
      * eauto.
      * exists [], SError. apply sstep_error_iff. auto.
      * exists [], SError. apply sstep_error_iff. split; [reflexivity|].
        right. apply unmodeled_at_cases. now left.
      * exfalso. destruct (Hlab _ _ TR0) as [Hl | [Hl | Hl]].
        -- apply val_inj in Hl. discriminate.
        -- apply val_inj in Hl. discriminate.
        -- apply Hl. constructor.
      * exists [], SError. apply sstep_error_iff. split; [reflexivity|].
        right. apply unmodeled_at_cases. now right.
    + intros evs c' Hs. destruct evs as [|e evs].
      * assert (TR : trans τ t (proc segs c')).
        { rewrite EQ. apply trans_proc_intro. left. eauto. }
        apply (proj1 (IH _ _ TR is_val_τ)). reflexivity.
      * assert (TR : trans (obs (Emit e) tt) t (emit_evs evs (Step (proc segs c')))).
        { rewrite EQ. apply trans_proc_intro. right; left. exists e, evs, c'. auto. }
        apply (proj2 (IH _ _ TR ltac:(apply is_val_obs)) evs). reflexivity.
  - intros pend c' EQ. destruct pend as [|e pend].
    + assert (TR : trans τ t (proc segs c')).
      { rewrite EQ. apply trans_step. }
      apply (proj1 (IH _ _ TR is_val_τ)). reflexivity.
    + assert (TR : trans (obs (Emit e) tt) t (emit_evs pend (Step (proc segs c')))).
      { rewrite EQ. apply trans_emit_cons. split; reflexivity. }
      apply (proj2 (IH _ _ TR ltac:(apply is_val_obs)) pend). reflexivity.
Qed.

Lemma ct_all_errors_all_traces_error c :
  ct_all_errors (proc segs c) -> all_traces_error segs c.
Proof. intros H. apply (proj1 (ct_all_traces_error _ H)). reflexivity. Qed.

(** No configuration reachable from [c] is blocked. *)
Definition block_free (c : config) : Prop :=
  forall tr c1, star segs c tr c1 -> ~ blocked_at c1.

Lemma block_free_step c evs c' :
  block_free c -> sstep segs c evs (SNext c') -> block_free c'.
Proof. intros Hbf Hs tr c1 Hst. apply (Hbf (evs ++ tr) c1). eapply star_step; eauto. Qed.

Lemma all_traces_error_ct c :
  block_free c -> all_traces_error segs c -> ct_all_errors (proc segs c).
Proof.
  intros Hbf H. revert Hbf. induction H as [c Hprog Hnext IH]. intros Hbf.
  assert (Hnb : ~ blocked_at c) by exact (Hbf [] c (star_refl segs c)).
  constructor.
  - destruct Hprog as (evs & [c'|] & Hs).
    + destruct evs as [|e evs].
      * exists τ, (proc segs c'). apply trans_proc_intro. left. eauto.
      * exists (obs (Emit e) tt), (emit_evs evs (Step (proc segs c'))).
        apply trans_proc_intro. right; left. exists e, evs, c'. auto.
    + destruct (sstep_error_trans _ _ Hs) as [Hb | (r & _ & TR)]; [contradiction | eauto].
  - intros l t' TR. apply trans_proc_inv in TR as
      [(? & _ & -> & _) | [(? & ? & ? & _ & -> & _)
      | [(_ & -> & _) | [(_ & -> & _) | [(Hh & -> & _) | (Hb & _)]]]]].
    + right; right. apply is_val_τ.
    + right; right. apply is_val_obs.
    + now left.
    + now right; left.
    + exfalso. destruct Hprog as (evs & st & Hs).
      exact (Hh (sstep_not_halted _ _ _ Hs)).
    + contradiction.
  - intros l t' TR Hnv. apply trans_proc_inv in TR as
      [(c' & Hs & _ & EQ) | [(e & evs & c' & Hs & _ & EQ)
      | [(_ & -> & _) | [(_ & -> & _) | [(_ & -> & _) | (Hb & _)]]]]];
      try (exfalso; apply Hnv; constructor); [| | contradiction].
    + rewrite EQ. exact (IH _ _ Hs (block_free_step _ _ _ Hbf Hs)).
    + rewrite EQ. apply ct_all_errors_emit_step.
      exact (IH _ _ Hs (block_free_step _ _ _ Hbf Hs)).
Qed.

(** On block-free runs the refinement is an equivalence. *)
Lemma block_free_iff c : block_free c ->
  (reaches_error segs c <-> ct_errors (proc segs c))
  /\ (reaches_unmodeled segs c <-> ct_unmodeled (proc segs c))
  /\ (all_traces_error segs c <-> ct_all_errors (proc segs c)).
Proof.
  intros Hbf. split; [|split].
  - split; [|apply ct_errors_reaches_error].
    intros H. destruct (reaches_error_ct _ H) as [? | (tr & c1 & Hst & Hb)]; [assumption|].
    exfalso. exact (Hbf _ _ Hst Hb).
  - split; [|apply ct_unmodeled_reaches_unmodeled].
    intros H. destruct (reaches_unmodeled_ct _ H) as [? | (tr & c1 & Hst & Hb)]; [assumption|].
    exfalso. exact (Hbf _ _ Hst Hb).
  - split; [exact (all_traces_error_ct c Hbf) | apply ct_all_errors_all_traces_error].
Qed.

(** A reachable blocked call: the tree walks there and diverges. *)
Lemma blocked_reach_diverges c tr c1 : star segs c tr c1 -> blocked_at c1 ->
  ct_path tr (proc segs c) (proc segs c1) /\ ct_diverges (proc segs c1).
Proof. intros Hst Hb. split; [apply star_path, Hst | apply blocked_diverges, Hb]. Qed.

(** One edge of [proc] per outcome of the pending call. *)
Definition outcome_edge (ms : machine_state) (model : Model) (i : SyscallInput)
    (o : Monad.outcome SyscallEffect) : @label procE * ptree result :=
  match o with
  | Monad.Unmodeled =>
      if would_block i model then (τ, proc segs (mkCfg ms model)) else (val RUnmodeled, Stuck)
  | Monad.Ok eff model' evs =>
      match outcome_next ms eff model' evs with
      | Some ([], c') => (τ, proc segs c')
      | Some (e :: evs', c') => (obs (Emit e) tt, emit_evs evs' (Step (proc segs c')))
      | None => (val RFault, Stuck)
      end
  end.

(** [proc] is finitely branching up to [equ]. *)
Theorem proc_fin_branching c :
  exists L : list (@label procE * ptree result),
    forall l t', trans l (proc segs c) t' -> exists t'', In (l, t'') L /\ t' ≅ t''.
Proof.
  destruct c as [ms model].
  destruct (m_halted model) as [code|] eqn:Hh.
  { exists [(val RHalt, Stuck)]. intros l t' TR.
    rewrite (proc_unfold segs (mkCfg ms model)) in TR.
    cbn [Monad.bind ctree_Monad] in TR. fold kont in TR.
    cbn [step_tree] in TR. rewrite Hh, bind_ret_l in TR.
    cbv beta iota delta [kont] in TR. apply trans_ret_inv in TR as [EQ ->].
    exists Stuck. split; [now left | exact EQ]. }
  destruct (ms_svc_pending ms) as [x8|] eqn:Hp.
  2:{ destruct (mi_account_step segs ms model) as [[ms' model']| |] eqn:Hs;
      [exists [(τ, proc segs (mkCfg ms' model'))] | exists [(val RFault, Stuck)]
      | exists [(val RUnmodeled, Stuck)]];
      intros l t' TR; rewrite (proc_unfold segs (mkCfg ms model)) in TR;
      cbn [Monad.bind ctree_Monad] in TR; fold kont in TR; cbn [step_tree] in TR;
      rewrite Hh, Hp, Hs, bind_ret_l in TR; cbv beta iota delta [kont] in TR.
      - apply trans_step_iff in TR as [-> EQ]. eexists. split; [now left | exact EQ].
      - apply trans_ret_inv in TR as [EQ ->]. eexists. split; [now left | exact EQ].
      - apply trans_ret_inv in TR as [EQ ->]. eexists. split; [now left | exact EQ]. }
  destruct (syscall_spec_finite (sys_input segs ms x8) model) as [lo Hlo].
  exists (List.map (outcome_edge ms model (sys_input segs ms x8)) lo).
  intros l t' TR. rewrite (proc_unfold segs (mkCfg ms model)) in TR.
  cbn [Monad.bind ctree_Monad] in TR. fold kont in TR.
  cbn [step_tree] in TR. rewrite Hh, Hp in TR.
  rewrite bind_br in TR. apply trans_br_inv in TR as [[o Ho] TR]. cbn [proj1_sig] in TR.
  pose proof (in_map (outcome_edge ms model (sys_input segs ms x8)) _ _ (Hlo o Ho)) as Hin.
  destruct o as [eff model' evs|]; cbn [outcome_tree outcome_edge] in TR, Hin.
  - destruct (outcome_next ms eff model' evs) as [[[|e evs'] c']|] eqn:Hon.
    + rewrite emit_ret_kont in TR. cbn [emit_evs] in TR.
      apply trans_step_iff in TR as [-> EQ]. eexists. split; [exact Hin | exact EQ].
    + rewrite emit_ret_kont in TR. apply trans_emit_cons in TR as [-> EQ].
      eexists. split; [exact Hin | exact EQ].
    + rewrite bind_ret_l in TR. cbv beta iota delta [kont] in TR.
      apply trans_ret_inv in TR as [EQ ->]. eexists. split; [exact Hin | exact EQ].
  - destruct (would_block (sys_input segs ms x8) model);
      rewrite bind_ret_l in TR; cbv beta iota delta [kont] in TR.
    + apply trans_step_iff in TR as [-> EQ]. eexists. split; [exact Hin | exact EQ].
    + apply trans_ret_inv in TR as [EQ ->]. eexists. split; [exact Hin | exact EQ].
Qed.

End WithSegs.

(* =========================================================================
   [Run.run] and [ct_run]
   ========================================================================= *)

(** [bt] (a tree's behavior) refines [br] (a run's): the same traces, and
    each error fact of [bt] is one of [br]. *)
Record refines (bt br : behavior) : Prop := mkRefines {
  rf_traces     : forall tr, bh_traces bt tr <-> bh_traces br tr;
  rf_errors     : bh_errors bt -> bh_errors br;
  rf_all_errors : bh_all_errors bt -> bh_all_errors br;
  rf_unmodeled  : bh_unmodeled bt -> bh_unmodeled br }.

Theorem ct_run_refines_run img lim en inp : refines (ct_run img lim en inp) (run img lim en inp).
Proof.
  destruct img as [segs pc ph], en as [sp brk0 mbase rnd].
  unfold ct_run, ct_behavior; cbn. constructor; cbn.
  - intros tr. symmetry. apply obs_trace_iff.
  - apply ct_errors_reaches_error.
  - apply ct_all_errors_all_traces_error.
  - apply ct_unmodeled_reaches_unmodeled.
Qed.

(** The run reaches a blocked call. *)
Definition run_blocked (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      exists tr c1, star segs (init_config segs pc ph sp brk0 mbase rnd lim inp) tr c1
                    /\ blocked_at segs c1
  end.

(** The run reaches no blocked call. *)
Definition run_block_free (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      block_free segs (init_config segs pc ph sp brk0 mbase rnd lim inp)
  end.

Theorem run_errors_ct img lim en inp :
  bh_errors (run img lim en inp) ->
  bh_errors (ct_run img lim en inp) \/ run_blocked img lim en inp.
Proof.
  destruct img as [segs pc ph], en as [sp brk0 mbase rnd].
  unfold ct_run, ct_behavior; cbn. apply reaches_error_ct.
Qed.

Theorem run_unmodeled_ct img lim en inp :
  bh_unmodeled (run img lim en inp) ->
  bh_unmodeled (ct_run img lim en inp) \/ run_blocked img lim en inp.
Proof.
  destruct img as [segs pc ph], en as [sp brk0 mbase rnd].
  unfold ct_run, ct_behavior; cbn. apply reaches_unmodeled_ct.
Qed.

(** Every blocked call the run reaches is an infinite [τ] path of the tree. *)
Theorem run_blocked_diverges img lim en inp : run_blocked img lim en inp ->
  exists tr u, ct_path tr (proc_run img lim en inp) u /\ ct_diverges u.
Proof.
  destruct img as [segs pc ph], en as [sp brk0 mbase rnd]. cbn.
  intros (tr & c1 & Hst & Hb). exists tr, (proc segs c1).
  exact (blocked_reach_diverges _ _ _ _ Hst Hb).
Qed.

Theorem run_ct_run_block_free img lim en inp : run_block_free img lim en inp ->
  behavior_equiv (run img lim en inp) (ct_run img lim en inp).
Proof.
  destruct img as [segs pc ph], en as [sp brk0 mbase rnd].
  unfold behavior_equiv, ct_run, ct_behavior; cbn. intros Hbf.
  destruct (block_free_iff _ _ Hbf) as (HE & HU & HA).
  split; [|split; [|split]]; auto.
  intros tr. apply obs_trace_iff.
Qed.

Lemma modeled_run_ct img lim en inp :
  modeled (run img lim en inp) -> modeled (ct_run img lim en inp).
Proof. intros H Hu. exact (H (rf_unmodeled _ _ (ct_run_refines_run img lim en inp) Hu)). Qed.

Lemma error_free_run_ct img lim en inp :
  error_free (run img lim en inp) -> error_free (ct_run img lim en inp).
Proof. intros H He. exact (H (rf_errors _ _ (ct_run_refines_run img lim en inp) He)). Qed.

Lemma trace_equiv_iff imgS limS enS imgT limT enT inp :
  trace_equiv (bh_traces (run imgS limS enS inp)) (bh_traces (run imgT limT enT inp))
  <-> trace_equiv (bh_traces (ct_run imgS limS enS inp))
                  (bh_traces (ct_run imgT limT enT inp)).
Proof.
  pose proof (rf_traces _ _ (ct_run_refines_run imgS limS enS inp)) as HS.
  pose proof (rf_traces _ _ (ct_run_refines_run imgT limT enT inp)) as HT.
  unfold trace_equiv. split; intros H tr.
  - rewrite HS, HT. apply H.
  - rewrite <- HS, <- HT. apply H.
Qed.

Lemma equiv_iff imgS limS enS imgT limT enT inp :
  run_block_free imgS limS enS inp -> run_block_free imgT limT enT inp ->
  (equiv (run imgS limS enS inp) (run imgT limT enT inp)
   <-> equiv (ct_run imgS limS enS inp) (ct_run imgT limT enT inp)).
Proof.
  intros HbS HbT; apply equiv_behavior_equiv.
  - now apply run_ct_run_block_free.
  - now apply run_ct_run_block_free.
Qed.

Section Spec.

Variable source_image : Image.
Variable target_image : Image.

(** [Equivalence.strong_equiv] over the tree model. *)
Definition ct_strong_equiv (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  modeled (ct_run source_image source_alloc_limit en_source inp)
  /\ equiv (ct_run source_image source_alloc_limit en_source inp)
           (ct_run target_image target_alloc_limit en_target inp).

Lemma strong_equiv_iff en_source en_target inp :
  run_block_free source_image source_alloc_limit en_source inp ->
  run_block_free target_image target_alloc_limit en_target inp ->
  (strong_equiv source_image target_image en_source en_target inp
   <-> ct_strong_equiv en_source en_target inp).
Proof.
  intros HbS HbT. unfold strong_equiv, ct_strong_equiv, modeled.
  destruct (run_ct_run_block_free _ _ _ _ HbS) as (_ & _ & _ & HU).
  rewrite HU, (equiv_iff _ _ _ _ _ _ _ HbS HbT). reflexivity.
Qed.

Definition ct_strong_universal_T : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    ct_strong_equiv en_source en_target inp.

Lemma strong_universal_iff :
  (forall en_source en_target inp,
     valid_entry source_image en_source inp -> valid_entry target_image en_target inp ->
     valid_input inp ->
     run_block_free source_image source_alloc_limit en_source inp
     /\ run_block_free target_image target_alloc_limit en_target inp) ->
  (strong_universal_T source_image target_image <-> ct_strong_universal_T).
Proof.
  intros Hbf. unfold strong_universal_T, ct_strong_universal_T.
  split; intros H en_source en_target inp Hs Ht Hi;
    destruct (Hbf _ _ _ Hs Ht Hi) as [HbS HbT];
    apply (strong_equiv_iff _ _ _ HbS HbT); apply H; assumption.
Qed.

(** [Equivalence.strong_equiv_error_free] over the tree model. *)
Definition ct_strong_equiv_error_free (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  error_free (ct_run source_image source_alloc_limit en_source inp)
  /\ error_free (ct_run target_image target_alloc_limit en_target inp)
  /\ trace_equiv
       (bh_traces (ct_run source_image source_alloc_limit en_source inp))
       (bh_traces (ct_run target_image target_alloc_limit en_target inp)).

Lemma strong_equiv_error_free_iff en_source en_target inp :
  run_block_free source_image source_alloc_limit en_source inp ->
  run_block_free target_image target_alloc_limit en_target inp ->
  (strong_equiv_error_free source_image target_image en_source en_target inp
   <-> ct_strong_equiv_error_free en_source en_target inp).
Proof.
  intros HbS HbT.
  unfold strong_equiv_error_free, ct_strong_equiv_error_free, error_free.
  destruct (run_ct_run_block_free _ _ _ _ HbS) as (_ & HES & _ & _).
  destruct (run_ct_run_block_free _ _ _ _ HbT) as (_ & HET & _ & _).
  rewrite HES, HET.
  rewrite (trace_equiv_iff source_image source_alloc_limit en_source
             target_image target_alloc_limit en_target inp).
  reflexivity.
Qed.

Definition ct_strong_universal_error_free_T : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    ct_strong_equiv_error_free en_source en_target inp.

Lemma strong_universal_error_free_iff :
  (forall en_source en_target inp,
     valid_entry source_image en_source inp -> valid_entry target_image en_target inp ->
     valid_input inp ->
     run_block_free source_image source_alloc_limit en_source inp
     /\ run_block_free target_image target_alloc_limit en_target inp) ->
  (strong_universal_error_free_T source_image target_image
   <-> ct_strong_universal_error_free_T).
Proof.
  intros Hbf. unfold strong_universal_error_free_T, ct_strong_universal_error_free_T.
  split; intros H en_source en_target inp Hs Ht Hi;
    destruct (Hbf _ _ _ Hs Ht Hi) as [HbS HbT];
    apply (strong_equiv_error_free_iff _ _ _ HbS HbT); apply H; assumption.
Qed.

(** Strongly bisimilar trees discharge the equivalence clause of
    [strong_equiv] once the source run is modeled and the target run
    never errors. *)
Lemma sbisim_strong_equiv en_s en_t inp :
  sbisim eq (proc_run source_image source_alloc_limit en_s inp)
            (proc_run target_image target_alloc_limit en_t inp) ->
  modeled (run source_image source_alloc_limit en_s inp) ->
  error_free (run target_image target_alloc_limit en_t inp) ->
  strong_equiv source_image target_image en_s en_t inp.
Proof.
  intros EQ Hm Hef. split; [exact Hm|]. right.
  destruct (ct_behavior_sbisim _ _ EQ) as (HT & _).
  split; [|exact Hef].
  apply (trace_equiv_iff source_image source_alloc_limit en_s
           target_image target_alloc_limit en_t inp).
  exact HT.
Qed.

End Spec.
