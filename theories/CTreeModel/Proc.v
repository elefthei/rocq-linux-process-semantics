(** * CTreeModel.Proc — the process of [Run.run] as a choice tree

    A second semantics of the process of [LinuxProcessSem.Run], written as
    a choice tree (vellvm/ctrees) instead of the relation [Run.sstep].
    [RunRefine] proves the tree refines [Run.run] and is equivalent to it
    on runs that reach no blocking call.

    The shape, one [Run.sstep] at a time ([step_tree]):

    - a halted model returns [RHalt];
    - an instruction step is deterministic: [Ret] of the next
      configuration, of [RFault] or of [RUnmodeled];
    - a pending syscall is ONE [Br] over every outcome
      [Specs.syscall_spec] admits ([procB]), followed by the outcome's
      events, one [Vis (Emit e)] node each ([emit_evs]), so trace
      prefixes at byte granularity are ctree paths.  A declined outcome
      whose shape [Block.would_block] recognizes as a wait returns the
      SAME configuration, so [proc] takes a [τ] back to itself forever —
      the kernel's wait loop with nothing to wake it
      ([RunRefine.blocked_diverges]); every other decline is
      [Ret RUnmodeled].

    [proc] iterates [step_tree] with [CTree.iterS], which puts a VISIBLE
    [Step] (a [τ] transition) after every step.  This matters for
    [Run.all_traces_error], which is divergence-sensitive: with the
    invisible [Guard] of [CTree.iter], a branch that diverges silently
    would have no transition at all and would vanish next to an
    erroring sibling.  With a [τ] per step, the transitions of [proc] are
    in lockstep with [Run.sstep] ([RunRefine.trans_proc_iff]). *)

From Stdlib Require Import ZArith NArith List.
From CTree Require Import CTree Eq.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.CTreeModel Require Import Block.
Import ListNotations CTree.
Open Scope ctree.
(* ctrees is universe polymorphic; so is this model, so that every use of
   [ptree] can share the levels of the trees it is compared with.  No
   minimization to [Set]: [Monad.bind] puts both value types in the one
   universe of [Monad.Monad], so [proc]'s [result] must be able to sit
   with [config]. *)
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(** Choice trees are a [Monad.Monad], so the process model's
    [x <- c ;; k] (sys_scope) also builds trees. *)
#[global] Instance ctree_Monad {E C} : Monad.Monad (ctree E C) := {
  pure A x := Ret x;
  bind A B c k := CTree.bind c k
}.

(** The only visible event: one byte-level [State.event]. *)
Variant procE : Type -> Type := Emit (ev : event) : procE unit.

(** The only branching: the outcomes [syscall_spec] admits for input [i]
    in model [m].  An empty set gives a [Br] with no transitions, as an
    outcome-less syscall gives no [Run.sstep]. *)
Variant procB : Type -> Type :=
  Choose (i : SyscallInput) (m : Model)
    : procB {o : Monad.outcome SyscallEffect | syscall_spec i m o}.

(** How a run ends.  [RUnmodeled] is [Run.unmodeled_at] outside the
    blocked shapes ([RunRefine.declined_at]); [RFault] is every other
    [SError] rule of [Run.sstep]. *)
Inductive result := RHalt | RFault | RUnmodeled.

Abbreviation ptree := (ctree procE procB).

Fixpoint emit_evs {X} (evs : list event) (k : ptree X) : ptree X :=
  match evs with
  | [] => k
  | e :: evs => Vis (Emit e) (fun _ => emit_evs evs k)
  end.

(* The deterministic part of the three Ok-rules of [Run.sstep]
   ([sstep_syscall] / [sstep_exit] / [sstep_killed]); [None] is
   [sstep_syscall_materialization_fault].  [m_killed m' = Some sig] implies
   [m_halted m' = Some sig] (State.m_killed), so the nested match is exhaustive
   and disjoint exactly like the rules. *)
Definition outcome_next (ms : machine_state) (eff : SyscallEffect)
    (model' : Model) (evs : list event) : option (list event * config) :=
  match m_halted model' with
  | None =>
      match materialize_model_accesses model' (syscall_effect_accesses eff) with
      | Some model'' =>
          Some (evs, mkCfg (advance_past_svc (apply_effect ms eff)) model'')
      | None => None
      end
  | Some code =>
      match m_killed model' with
      | None => Some (evs ++ [ExitEv code (m_fs model')], mkCfg ms model')
      | Some sig => Some (evs ++ [KillEv sig (m_fs model')], mkCfg ms model')
      end
  end.

(** A declined outcome whose shape [Block.would_block] recognizes as a
    wait returns the SAME configuration: [proc] then takes a [τ] back to
    itself forever, the kernel's wait loop with nothing to wake it. *)
Definition outcome_tree (i : SyscallInput) (ms : machine_state) (model : Model)
    (o : Monad.outcome SyscallEffect) : ptree (config + result) :=
  match o with
  | Monad.Unmodeled =>
      if would_block i model then Ret (inl (mkCfg ms model)) else Ret (inr RUnmodeled)
  | Monad.Ok eff model' evs =>
      match outcome_next ms eff model' evs with
      | Some (evs', c') => emit_evs evs' (Ret (inl c'))
      | None => Ret (inr RFault)
      end
  end.

(** One [Run.sstep]. *)
Definition step_tree (segs : list Segment) (c : config)
    : ptree (config + result) :=
  match c with mkCfg ms model =>
  match m_halted model with
  | Some _ => Ret (inr RHalt)
  | None =>
      match ms_svc_pending ms with
      | None =>
          match mi_account_step segs ms model with
          | MachineOk (ms', model') => Ret (inl (mkCfg ms' model'))
          | MachineFault => Ret (inr RFault)
          | MachineUnmodeled => Ret (inr RUnmodeled)
          end
      | Some x8 =>
          Br (Choose (sys_input segs ms x8) model)
             (fun ox => outcome_tree (sys_input segs ms x8) ms model (proj1_sig ox))
      end
  end end.

Definition proc (segs : list Segment) : config -> ptree result :=
  CTree.iterS (step_tree segs).

(** The tree of [Run.run img lim en inp]. *)
Definition proc_run (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput)
    : ptree result :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      proc segs (init_config segs pc ph sp brk0 mbase rnd lim inp)
  end.

(* =========================================================================
   Unfolding and structural transitions
   ========================================================================= *)

Lemma unfold_iterS {E B R I} (step : I -> ctree E B (I + R)) i :
  CTree.iterS step i ≅
    (lr <- step i ;;
     match lr with inl l => Step (CTree.iterS step l) | inr r => Ret r end).
Proof. now step. Qed.

(** Only ever [rewrite proc_unfold]; never unfold [proc] (a [cofix]). *)
Lemma proc_unfold segs c :
  proc segs c ≅
    (lr <- step_tree segs c ;;
     match lr with inl c' => Step (proc segs c') | inr r => Ret r end).
Proof. exact (unfold_iterS (step_tree segs) c). Qed.

Lemma trans_emit_cons {X} e evs (k : ptree X) l t' :
  trans l (emit_evs (e :: evs) k) t' <->
  l = obs (Emit e) tt /\ t' ≅ emit_evs evs k.
Proof.
  split.
  - intros TR. apply trans_vis_inv in TR as ([] & EQ & ->). now split.
  - intros [-> EQ]. cbn. rewrite EQ. apply (trans_vis (Emit e) tt).
Qed.

Lemma trans_step_iff {X} (u : ptree X) l t' :
  trans l (Step u) t' <-> l = τ /\ t' ≅ u.
Proof.
  split.
  - intros TR. apply trans_step_inv in TR as [EQ ->]. now split.
  - intros [-> EQ]. rewrite EQ. apply trans_step.
Qed.
