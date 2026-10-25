(** * CTreeModel.InfRefine — infinite behaviors of a [Proc.ptree] refine
    the finite traces of [Run.run]

    [RunRefine.ct_run_refines_run] relates the four fields of
    [Run.behavior] (traces coincide; the tree's error facts imply the
    run's), all of which are FINITE observations: prefixes ([Run.obs_trace]) and
    reachability / inductive must-error facts.  A choice tree says more:
    it has infinite paths.  Two infinite observations are defined here:

    - [ct_inf_trace t s]: [t] has a path emitting the infinite stream
      [s], each event reached after finitely many [τ] steps (productive);
    - [ct_diverges t]: [t] has an infinite path of [τ] steps (silent
      divergence).  [Run.behavior] cannot tell this from a tree with no
      transition at all ([Stuck]).

    The original model has no infinite traces to be equal TO, so the
    relation to it is a refinement, not an equivalence: an infinite trace
    of the tree is admitted by the original model when every finite
    prefix of it is ([inf_refines]).  The converse — every stream whose
    prefixes all lie in [Run.obs_trace] is an infinite path of the tree —
    is König's lemma; the tree is finitely branching
    ([RunRefine.proc_fin_branching]), but König's lemma also needs
    classical reasoning, which this development does not assume. *)

From Stdlib Require Import ZArith List Streams.
From CTree Require Import CTree Eq.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State Run.
From LinuxProcessSemantics.CTreeModel Require Import Proc Behavior RunRefine.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
Import ListNotations CTree.
Set Universe Polymorphism.

(** Every finite prefix of an infinite trace is a finite trace. *)
Lemma ct_inf_trace_prefix t s n : ct_inf_trace t s -> ct_traces t (stream_prefix n s).
Proof.
  revert t s; induction n as [|n IH]; intros t s [e s' t' u P H]; cbn.
  - exists t'. now constructor.
  - destruct (IH _ _ H) as [w Pw]. exists w. exact (ct_path_app _ _ _ _ _ P Pw).
Qed.

(** A silent divergence after [tr] is observed by the finite model only
    as [tr], the same as a deadlock after [tr]. *)
Lemma ct_diverges_after tr t u : ct_path tr t u -> ct_diverges u -> ct_traces t tr.
Proof. intros P _. now exists u. Qed.

(** Infinite traces of [proc] refine [Run.obs_trace]. *)
Theorem proc_inf_refines segs c s :
  ct_inf_trace (proc segs c) s -> inf_refines (obs_trace segs c) s.
Proof. intros H n. apply obs_trace_iff, ct_inf_trace_prefix, H. Qed.

(** Infinite traces of [proc_run] refine the finite traces of [Run.run]. *)
Theorem ct_run_inf_refines img lim en inp s :
  ct_inf_trace (proc_run img lim en inp) s ->
  inf_refines (bh_traces (run img lim en inp)) s.
Proof.
  intros H n. apply (rf_traces _ _ (ct_run_refines_run img lim en inp)), ct_inf_trace_prefix, H.
Qed.

(** A divergence of [proc_run] after [tr] is seen by [Run.run] as [tr]. *)
Theorem ct_run_diverges_refines img lim en inp tr u :
  ct_path tr (proc_run img lim en inp) u -> ct_diverges u ->
  bh_traces (run img lim en inp) tr.
Proof.
  intros P D. apply (rf_traces _ _ (ct_run_refines_run img lim en inp)).
  exact (ct_diverges_after _ _ _ P D).
Qed.

(** A blocked call the run reaches: its trace so far is a trace of the
    run, after which the tree diverges. *)
Theorem run_blocked_inf img lim en inp : run_blocked img lim en inp ->
  exists tr, bh_traces (run img lim en inp) tr
    /\ exists u, ct_path tr (proc_run img lim en inp) u /\ ct_diverges u.
Proof.
  intros Hb. destruct (run_blocked_diverges _ _ _ _ Hb) as (tr & u & P & D).
  exists tr. split; [exact (ct_run_diverges_refines _ _ _ _ _ _ P D) | eauto].
Qed.

(** Refinement transports along [trace_equiv]. *)
Lemma inf_refines_trace_equiv T1 T2 s :
  trace_equiv T1 T2 -> inf_refines T1 s -> inf_refines T2 s.
Proof. intros E H n. apply E, H. Qed.

(** The infinite-trace reading of [Equivalence.equiv]: outside the escape,
    every infinite trace of the TARGET's tree is admitted by the SOURCE's
    finite traces (a refinement: the source need not have that path itself). *)
Theorem equiv_target_inf_refines_source imgS limS enS imgT limT enT inp s :
  equiv (run imgS limS enS inp) (run imgT limT enT inp) ->
  ~ bh_all_errors (run imgS limS enS inp) ->
  ct_inf_trace (proc_run imgT limT enT inp) s ->
  inf_refines (bh_traces (run imgS limS enS inp)) s.
Proof.
  intros [A|[E _]] N H; [contradiction|].
  apply (inf_refines_trace_equiv (bh_traces (run imgT limT enT inp))).
  - intros tr. symmetry. apply E.
  - now apply ct_run_inf_refines.
Qed.

(** Symmetrically, infinite traces of the SOURCE's tree are admitted by the
    TARGET's finite traces. *)
Theorem equiv_source_inf_refines_target imgS limS enS imgT limT enT inp s :
  equiv (run imgS limS enS inp) (run imgT limT enT inp) ->
  ~ bh_all_errors (run imgS limS enS inp) ->
  ct_inf_trace (proc_run imgS limS enS inp) s ->
  inf_refines (bh_traces (run imgT limT enT inp)) s.
Proof.
  intros [A|[E _]] N H; [contradiction|].
  exact (inf_refines_trace_equiv _ _ _ E (ct_run_inf_refines _ _ _ _ _ H)).
Qed.
