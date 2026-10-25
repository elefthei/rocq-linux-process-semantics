(** * CTreeModel.Block — which declines are waits, and that the finite
    model only declines there

    The finite model answers [Unmodeled] where Linux would sleep, because
    it has no step that resumes a sleeper.  [would_block i m] is the
    computable list of those shapes; [Proc] treats them as a wait that
    never returns (a [τ] self-loop).  Two classes, named per call below:

    - CERTAIN: in this model's closed world — one thread, no signal
      sources, no other process — the call provably never returns;
    - MAY-BLOCK: the model lacks the state that decides whether Linux
      returns; the tree over-approximates the wait as infinite.

    [would_block] is deliberately a hand-written list: its COMPLETENESS is
    a modeling judgment, its SOUNDNESS ([would_block_declined]: the finite
    model's only outcome there is [Unmodeled]) is a theorem.

    Excluded on purpose:
    - timed waits (FUTEX_WAIT with a timeout, ppoll/pselect6 with a
      deadline): Linux returns;
    - [connect]: success, refusal and timeout mixed;
    - [getrandom] with GRND_RANDOM: the pool refills;
    - [nanosleep]: modeled;
    - [accept]: the model's queue cannot be empty;
    - [epoll_pwait], eventfd, timerfd: no descriptor kind to wait on;
    - [wait4(WNOHANG)] with children: missing reap state, not a wait. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Progress.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.
Local Open Scope Z_scope.

(** include/uapi/linux/wait.h; not in [Sys.Uapi]. *)
Definition WUNTRACED : Z := 2.
Definition WCONTINUED : Z := 8.
Definition P_ALL : Z := 0.
Definition WEXITED : Z := 4.

(** [flock] (32), MAY-BLOCK: a blocking LOCK_SH/LOCK_EX on a regular file
    another descriptor names; whether that one holds a conflicting lock is
    state the model does not carry. *)
Definition flock_blocks (i : SyscallInput) (m : Model) : bool :=
  negb (flock_mand_b (cmd32 (in_arg i 1))) && flock_cmd_ok_b (cmd32 (in_arg i 1))
  && negb (flock_unlock_b (cmd32 (in_arg i 1)))
  && Z.eqb (Z.land (bv_unsigned (cmd32 (in_arg i 1))) LOCK_NB) 0
  && match fd_lookup (m_fds m) (fd32 (in_arg i 0)) with
     | Some (FdFile p _) | Some (FdFileW p _) | Some (FdFileA p _)
     | Some (FdFileRW p _) => negb (flock_sole_opener (m_fds m) p)
     | _ => false
     end.

(** [read] (63), CERTAIN: an empty pipe whose only writers are this
    process's own descriptors. *)
Definition read_blocks (i : SyscallInput) (m : Model) : bool :=
  match fd_lookup (m_fds m) (fd32 (in_arg i 0)) with
  | Some (FdPipe id false) =>
      modeled_rw_range (in_arg i 1) (in_arg i 2) && negb (w_is0 (in_arg i 2))
      && match pipe_lookup (m_pipes m) id with
         | Some ([], _) => pipe_end_live (m_fds m) id true
         | _ => false
         end
  | _ => false
  end.

(** [write] (64), MAY-BLOCK: a pipe write past the one ring slot the
    model accounts for. *)
Definition write_blocks (i : SyscallInput) (m : Model) : bool :=
  match fd_lookup (m_fds m) (fd32 (in_arg i 0)) with
  | Some (FdPipe id true) =>
      modeled_rw_range (in_arg i 1) (in_arg i 2) && negb (w_is0 (in_arg i 2))
      && pipe_end_live (m_fds m) id false
      && match pipe_lookup (m_pipes m) id with
         | Some st => negb (pipe_write_room st (bv_unsigned (in_arg i 2)))
         | None => false
         end
  | _ => false
  end.

(** [pselect6] (72), CERTAIN: nothing ready, no timeout, no signal mask. *)
Definition pselect6_blocks (i : SyscallInput) (m : Model) : bool :=
  match pselect_sigpack (in_mem i) (in_arg i 5), pselect_timeout (in_mem i) (in_arg i 4) with
  | PsSigNone, PsToNone =>
      match pselect_core i m (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) with
      | PsCoreDone ret _ => Z.eqb ret 0
      | _ => false
      end
  | _, _ => false
  end.

(** [ppoll] (73), CERTAIN: nothing ready, no timeout, no signal mask. *)
Definition ppoll_blocks (i : SyscallInput) (m : Model) : bool :=
  match pselect_timeout (in_mem i) (in_arg i 2) with
  | PsToNone =>
      match ppoll_sigmask (in_mem i) (in_arg i 3) (in_arg i 4) with
      | PpSigNone =>
          match ppoll_core i m (in_arg i 0) (unfds32 (in_arg i 1)) with
          | PsCoreDone ret _ => Z.eqb ret 0
          | _ => false
          end
      | _ => false
      end
  | _ => false
  end.

(** [waitid] (95), MAY-BLOCK, no arm: [waitid(P_ALL, _, _, WEXITED)] with
    a child the model cannot step. *)
Definition waitid_blocks (i : SyscallInput) (m : Model) : bool :=
  Z.eqb (bv_unsigned (in_arg i 0)) P_ALL && Z.eqb (bv_unsigned (in_arg i 3)) WEXITED
  && m_has_children m.

(** [futex] (98), CERTAIN: FUTEX_WAIT_PRIVATE, no timeout, the word holds
    [val]; nothing can wake the only thread. *)
Definition futex_blocks (i : SyscallInput) (m : Model) : bool :=
  bv_eqb (in_arg i 1) (Z_to_bv 64 FUTEX_WAIT_PRIVATE) && w_is0 (in_arg i 3)
  && futex_aligned_b (in_arg i 0) && access_okb (in_arg i 0) FUTEX_WORD_SIZE
  && match read_bytes_map (in_mem i) (in_arg i 0) (Z_to_bv 64 FUTEX_WORD_SIZE) with
     | Some uval => bv_eqb (le_bytes_to_word uval) (abi_low32 (in_arg i 2))
     | None => false
     end.

(** [rt_sigsuspend] (133), CERTAIN, no arm: a well-formed call, and no
    pending blocked SIGABRT (the model's only deliverable signal).  A bad
    sigsetsize or an unreadable mask is -EINVAL/-EFAULT at once. *)
Definition rt_sigsuspend_blocks (i : SyscallInput) (m : Model) : bool :=
  Z.eqb (bv_unsigned (in_arg i 1)) 8
  && match read_u64 (in_mem i) (in_arg i 0) with Some _ => true | None => false end
  && negb (m_sigabrt_pending m).

(** [wait4] (260), MAY-BLOCK: [wait4(-1, _, 0 or WUNTRACED|WCONTINUED, _)]
    with a child the model cannot step. *)
Definition wait4_blocks (i : SyscallInput) (m : Model) : bool :=
  Z.eqb (bv_unsigned (pid32 (in_arg i 0))) WAIT_ANY32
  && Z.eqb (Z.land (bv_unsigned (waitopts32 (in_arg i 2))) WNOHANG) 0
  && Z.eqb (Z.land (bv_unsigned (waitopts32 (in_arg i 2)))
                   (Z.lnot (Z.lor WUNTRACED WCONTINUED))) 0
  && m_has_children m.

Definition would_block (i : SyscallInput) (m : Model) : bool :=
  let n := bv_unsigned (in_sysno i) in
  if Z.eqb n 32 then flock_blocks i m
  else if Z.eqb n 63 then read_blocks i m
  else if Z.eqb n 64 then write_blocks i m
  else if Z.eqb n 72 then pselect6_blocks i m
  else if Z.eqb n 73 then ppoll_blocks i m
  else if Z.eqb n 95 then waitid_blocks i m
  else if Z.eqb n 98 then futex_blocks i m
  else if Z.eqb n 133 then rt_sigsuspend_blocks i m
  else if Z.eqb n 260 then wait4_blocks i m
  else false.

(** ** Soundness: the finite model declines every shape above *)

Lemma bind_input {A} (k : SyscallInput -> Sys A) i m o :
  bind input k i m o <-> k i i m o.
Proof.
  unfold bind, input, Sys_Monad. destruct o as [x m2 evs|]; split.
  - intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3).
    injection H1 as -> -> ->. cbn in H3. subst evs. exact H2.
  - intros H. exists i, m, [], evs. auto.
  - intros [H | (x0 & m1 & evs1 & H1 & H2)]; [discriminate|].
    injection H1 as -> -> ->. exact H2.
  - intros H. right. exists i, m, []. auto.
Qed.

(** A bound [unmodeled] continuation leaves only [Unmodeled]. *)
Lemma record_copyins_unmodeled l i m o :
  record_copyins l unmodeled i m o -> o = Unmodeled.
Proof.
  unfold record_copyins, bind, unmodeled, Sys_Monad.
  destruct o; intros H; sys_destruct; try discriminate; reflexivity.
Qed.

(** The arm [syscall_spec] dispatches number [Hno] to. *)
Local Ltac arm H Hno :=
  unfold syscall_spec, dispatch in H; rewrite Hno in H;
  cbn [lookup_arm spec_table sa_no sa_spec Z.eqb Pos.eqb] in H.

Local Ltac bool_split :=
  repeat match goal with
  | Hx : (_ && _)%bool = true |- _ => apply andb_true_iff in Hx as [? ?]
  end.

Lemma flock_declined i m : flock_blocks i m = true -> bv_unsigned (in_sysno i) = 32 ->
  forall o, syscall_spec i m o -> o = Unmodeled.
Proof.
  intros Hb Hno o H. arm H Hno.
  unfold flock_spec in H. apply bind_get_model in H. cbv beta in H.
  unfold flock_blocks in Hb.
  destruct (flock_mand_b _) eqn:E1, (flock_cmd_ok_b _) eqn:E2, (flock_unlock_b _) eqn:E3;
    cbn [negb andb] in Hb; try discriminate Hb.
  apply andb_true_iff in Hb as [_ Hb].
  destruct (fd_lookup _ _) as [e|]; [|discriminate Hb].
  cbn beta iota in H.
  destruct e; try discriminate Hb; apply negb_true_iff in Hb; rewrite Hb in H; exact H.
Qed.

Lemma read_declined i m : read_blocks i m = true -> bv_unsigned (in_sysno i) = 63 ->
  forall o, syscall_spec i m o -> o = Unmodeled.
Proof.
  intros Hb Hno o H. arm H Hno.
  unfold read_spec in H. apply bind_input in H. apply bind_get_model in H. cbv beta in H.
  unfold read_blocks in Hb.
  destruct (fd_lookup _ _) as [[| | | | | | |id [|] | |]|]; try discriminate Hb.
  destruct (modeled_rw_range _ _), (w_is0 _); cbn [negb andb] in Hb; try discriminate Hb.
  destruct (pipe_lookup _ _) as [[[|b q] used]|]; try discriminate Hb.
  cbn beta iota in H. rewrite Hb in H. exact H.
Qed.

Lemma write_declined i m : write_blocks i m = true -> bv_unsigned (in_sysno i) = 64 ->
  forall o, syscall_spec i m o -> o = Unmodeled.
Proof.
  intros Hb Hno o H. arm H Hno.
  unfold write_spec in H. apply bind_input in H. apply bind_get_model in H. cbv beta in H.
  unfold write_blocks in Hb.
  destruct (fd_lookup _ _) as [[| | | | | | |id [|] | |]|]; try discriminate Hb.
  destruct (modeled_rw_range _ _), (w_is0 _), (pipe_end_live _ _ _);
    cbn [negb andb] in Hb; try discriminate Hb.
  destruct (pipe_lookup _ _) as [st|]; [|discriminate Hb].
  cbn beta iota in H. rewrite Hb in H. exact H.
Qed.

Lemma pselect6_declined i m : pselect6_blocks i m = true -> bv_unsigned (in_sysno i) = 72 ->
  forall o, syscall_spec i m o -> o = Unmodeled.
Proof.
  intros Hb Hno o H. arm H Hno.
  unfold pselect6_spec in H. apply bind_input in H. apply bind_get_model in H. cbv beta in H.
  unfold pselect6_blocks in Hb.
  assert (E : pselect6_outcome i m (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
                (in_arg i 3) (in_arg i 4) (in_arg i 5) = None).
  { unfold pselect6_outcome, pselect_finish.
    destruct (pselect_sigpack (in_mem i) (in_arg i 5)), (pselect_timeout (in_mem i) (in_arg i 4));
      try discriminate Hb.
    destruct (pselect_core i m (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3));
      try discriminate Hb.
    cbn beta iota zeta in Hb |- *. rewrite Hb. reflexivity. }
  rewrite E in H. exact H.
Qed.

Lemma ppoll_declined i m : ppoll_blocks i m = true -> bv_unsigned (in_sysno i) = 73 ->
  forall o, syscall_spec i m o -> o = Unmodeled.
Proof.
  intros Hb Hno o H. arm H Hno.
  unfold ppoll_spec in H. apply bind_input in H. apply bind_get_model in H. cbv beta in H.
  unfold ppoll_blocks in Hb.
  assert (E : ppoll_outcome i m (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2)
                (in_arg i 3) (in_arg i 4) = None).
  { unfold ppoll_outcome, pselect_finish.
    destruct (pselect_timeout (in_mem i) (in_arg i 2)); try discriminate Hb.
    destruct (ppoll_sigmask (in_mem i) (in_arg i 3) (in_arg i 4)); try discriminate Hb.
    destruct (ppoll_core i m (in_arg i 0) (unfds32 (in_arg i 1))); try discriminate Hb.
    cbn beta iota zeta in Hb |- *. rewrite Hb. reflexivity. }
  rewrite E in H. exact H.
Qed.

(** A number with no arm. *)
Local Ltac no_arm H Hno :=
  unfold syscall_spec, dispatch in H; rewrite Hno in H;
  cbn [lookup_arm spec_table sa_no Z.eqb Pos.eqb] in H; exact H.

Lemma waitid_declined i m : bv_unsigned (in_sysno i) = 95 ->
  forall o, syscall_spec i m o -> o = Unmodeled.
Proof. intros Hno o H. no_arm H Hno. Qed.

Lemma rt_sigsuspend_declined i m : bv_unsigned (in_sysno i) = 133 ->
  forall o, syscall_spec i m o -> o = Unmodeled.
Proof. intros Hno o H. no_arm H Hno. Qed.

Lemma futex_declined i m : futex_blocks i m = true -> bv_unsigned (in_sysno i) = 98 ->
  forall o, syscall_spec i m o -> o = Unmodeled.
Proof.
  intros Hb Hno o H. arm H Hno.
  unfold futex_blocks in Hb.
  destruct (bv_eqb (in_arg i 1) (Z_to_bv 64 FUTEX_WAIT_PRIVATE)) eqn:Eop; [|discriminate Hb].
  apply bv_eqb_eq in Eop.
  destruct (w_is0 (in_arg i 3)) eqn:Eu; [|discriminate Hb].
  destruct (futex_aligned_b (in_arg i 0)) eqn:Ea; [|discriminate Hb].
  destruct (access_okb (in_arg i 0) FUTEX_WORD_SIZE) eqn:Eok; [|discriminate Hb].
  cbn [andb] in Hb.
  unfold futex_spec, futex_wait_private_spec, futex_key_check in H.
  rewrite Eop, Eu, Ea, Eok in H.
  assert (W1 : bv_eqb (Z_to_bv 64 FUTEX_WAIT_PRIVATE) (Z_to_bv 64 FUTEX_WAKE_PRIVATE) = false)
    by reflexivity.
  assert (W2 : bv_eqb (Z_to_bv 64 FUTEX_WAIT_PRIVATE) (Z_to_bv 64 FUTEX_WAIT_PRIVATE) = true)
    by (apply bv_eqb_eq; reflexivity).
  rewrite W1, W2 in H.
  cbn [negb] in H. apply bind_input in H. cbv beta in H.
  destruct (read_bytes_map (in_mem i) (in_arg i 0) (Z_to_bv 64 FUTEX_WORD_SIZE)); [|discriminate Hb].
  rewrite Hb in H. exact (record_copyins_unmodeled _ _ _ _ H).
Qed.

Lemma wait4_declined i m : wait4_blocks i m = true -> bv_unsigned (in_sysno i) = 260 ->
  forall o, syscall_spec i m o -> o = Unmodeled.
Proof.
  intros Hb Hno o H. arm H Hno.
  unfold wait4_blocks in Hb. bool_split.
  unfold wait4_spec in H.
  match goal with Hx : Z.eqb (bv_unsigned (pid32 _)) _ = true |- _ => rewrite Hx in H end.
  destruct (Z.eqb (bv_unsigned (waitopts32 (in_arg i 2))) WNOHANG) eqn:E.
  - (* options = WNOHANG contradicts [options & WNOHANG = 0] *)
    apply Z.eqb_eq in E.
    match goal with Hx : Z.eqb (Z.land (bv_unsigned (waitopts32 _)) WNOHANG) 0 = true |- _ =>
      rewrite E in Hx; discriminate Hx end.
  - exact H.
Qed.

Theorem would_block_declined i m : would_block i m = true ->
  forall o, syscall_spec i m o -> o = Unmodeled.
Proof.
  unfold would_block. cbv zeta. intros Hb.
  set (n := bv_unsigned (in_sysno i)) in Hb.
  destruct (Z.eqb n 32) eqn:E; [apply Z.eqb_eq in E; exact (flock_declined i m Hb E)|].
  destruct (Z.eqb n 63) eqn:E'; [apply Z.eqb_eq in E'; exact (read_declined i m Hb E')|].
  destruct (Z.eqb n 64) eqn:E2; [apply Z.eqb_eq in E2; exact (write_declined i m Hb E2)|].
  destruct (Z.eqb n 72) eqn:E3; [apply Z.eqb_eq in E3; exact (pselect6_declined i m Hb E3)|].
  destruct (Z.eqb n 73) eqn:E4; [apply Z.eqb_eq in E4; exact (ppoll_declined i m Hb E4)|].
  destruct (Z.eqb n 95) eqn:E5; [apply Z.eqb_eq in E5; exact (waitid_declined i m E5)|].
  destruct (Z.eqb n 98) eqn:E6; [apply Z.eqb_eq in E6; exact (futex_declined i m Hb E6)|].
  destruct (Z.eqb n 133) eqn:E7; [apply Z.eqb_eq in E7; exact (rt_sigsuspend_declined i m E7)|].
  destruct (Z.eqb n 260) eqn:E8; [apply Z.eqb_eq in E8; exact (wait4_declined i m Hb E8)|].
  discriminate Hb.
Qed.

(** And [Unmodeled] really is admitted there ([Progress.receptive]). *)
Theorem would_block_unmodeled i m : would_block i m = true -> syscall_spec i m Unmodeled.
Proof.
  intros Hb. pose proof (receptive i m) as Ho.
  rewrite <- (would_block_declined i m Hb _ Ho). exact Ho.
Qed.
