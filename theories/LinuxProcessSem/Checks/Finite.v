(** * LinuxProcessSem.Checks.Finite — [syscall_spec] is finitely branching

    For every input and model, the outcomes [syscall_spec] admits fit in a
    finite list.  Proved per arm of [Sys.SyscallTable.spec_table] by closure
    of [fin_sys] under the monad combinators; every [choose] is over a finite
    type, a listed set, or byte lists of bounded length. *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import finite.
From stdpp.bitvector Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

Definition fin_pred {A} (P : A -> Prop) : Prop := exists l : list A, forall x, P x -> In x l.
Definition fin_sys {A} (c : Sys A) : Prop :=
  forall i m, exists l : list (outcome A), forall o, c i m o -> In o l.

(** ** Finite predicates *)

Lemma fin_pred_False {A} : fin_pred (fun _ : A => False).
Proof. exists []; tauto. Qed.

Lemma fin_pred_In {A} (es : list A) : fin_pred (fun x => In x es).
Proof. exists es; auto. Qed.

Lemma fin_pred_finite {A} `{Finite A} (P : A -> Prop) : fin_pred P.
Proof. exists (enum A); intros x _; apply list_elem_of_In, elem_of_enum. Qed.

Lemma fin_pred_sub {A} (P Q : A -> Prop) : (forall x, P x -> Q x) -> fin_pred Q -> fin_pred P.
Proof. intros H [l Hl]; exists l; auto. Qed.

Lemma fin_pred_len_eq (n : nat) : fin_pred (fun bs : list byte => length bs = n).
Proof.
  induction n as [|n [l Hl]].
  - exists [[]]; intros [|] H; [now left | discriminate].
  - exists (flat_map (fun b => map (cons b) l) (enum byte)).
    intros [|b bs] H; [discriminate|]; injection H as H.
    apply in_flat_map; exists b; split.
    + apply list_elem_of_In, elem_of_enum.
    + apply in_map, Hl, H.
Qed.

Lemma fin_pred_len_le (n : nat) : fin_pred (fun bs : list byte => (length bs <= n)%nat).
Proof.
  assert (Hk : forall k, exists l, forall bs : list byte, length bs = k -> In bs l)
    by (intro k; apply fin_pred_len_eq).
  induction n as [|n [l Hl]].
  - destruct (Hk 0%nat) as [l Hl]; exists l; intros x Hx; apply Hl; lia.
  - destruct (Hk (S n)) as [l' Hl']; exists (l' ++ l); intros x Hx; apply in_or_app.
    destruct (Nat.eq_dec (length x) (S n)); [left; auto | right; apply Hl; lia].
Qed.

Lemma fin_pred_len_leZ (z : Z) : fin_pred (fun bs : list byte => (Z.of_nat (length bs) <= z)%Z).
Proof. eapply fin_pred_sub; [|apply (fin_pred_len_le (Z.to_nat z))]; cbn; intros; lia. Qed.

(** ** Closure of [fin_sys] *)

Lemma fin_det {A} (c : Sys A) : (forall i m, exists o0, forall o, c i m o -> o = o0) -> fin_sys c.
Proof. intros H i m; destruct (H i m) as [o0 Ho]; exists [o0]; intros o Ho'; left; symmetry; auto. Qed.

Ltac fin_det_tac := apply fin_det; intros i m; eexists; intros o Ho; exact Ho.

Lemma fin_pure {A} (x : A) : fin_sys (pure x). Proof. fin_det_tac. Qed.
Lemma fin_unmodeled {A} : fin_sys (@unmodeled A). Proof. fin_det_tac. Qed.
Lemma fin_emit evs : fin_sys (emit evs). Proof. fin_det_tac. Qed.
Lemma fin_input : fin_sys input. Proof. fin_det_tac. Qed.
Lemma fin_sysno : fin_sys sysno. Proof. fin_det_tac. Qed.
Lemma fin_arg k : fin_sys (arg k). Proof. fin_det_tac. Qed.
Lemma fin_get_model : fin_sys get_model. Proof. fin_det_tac. Qed.
Lemma fin_get_fds : fin_sys get_fds. Proof. fin_det_tac. Qed.
Lemma fin_get_vmmaps : fin_sys get_vmmaps. Proof. fin_det_tac. Qed.
Lemma fin_modify f : fin_sys (modify f). Proof. fin_det_tac. Qed.

Lemma fin_alt {A} (c1 c2 : Sys A) : fin_sys c1 -> fin_sys c2 -> fin_sys (alt c1 c2).
Proof.
  intros H1 H2 i m; destruct (H1 i m) as [l1 ?], (H2 i m) as [l2 ?].
  exists (l1 ++ l2); intros o [|]; apply in_or_app; auto.
Qed.

Lemma fin_choose {A} (P : A -> Prop) : fin_pred P -> fin_sys (choose P).
Proof.
  intros [l Hl] i m; exists (map (fun x => Ok x m []) l).
  intros o (x & Hx & ->); apply (in_map (fun x => Ok x m [])), Hl, Hx.
Qed.

Lemma list_fin_concat {A B} (l : list A) (P : A -> list B -> Prop) :
  (forall a, In a l -> exists lb, P a lb) ->
  exists L, forall a, In a l -> exists lb, P a lb /\ incl lb L.
Proof.
  induction l as [|a l IH]; intros H.
  - exists []; intros _ [].
  - destruct (H a (or_introl eq_refl)) as [lb Hlb].
    destruct IH as [L' HL']; [intros; apply H; right; auto|].
    exists (lb ++ L'); intros a' [<-|Ha'].
    + exists lb; split; [auto | apply incl_appl, incl_refl].
    + destruct (HL' a' Ha') as (lb' & ? & ?); exists lb'; split; [auto | apply incl_appr; auto].
Qed.

Lemma fin_bind {A B} (c : Sys A) (k : A -> Sys B) :
  fin_sys c -> (forall x, fin_sys (k x)) -> fin_sys (bind c k).
Proof.
  intros Hc Hk i m; destruct (Hc i m) as [l Hl].
  destruct (list_fin_concat l (fun o lb => forall y m2 evs2,
      match o with Ok x m1 _ => k x i m1 (Ok y m2 evs2) -> In (Ok y m2 evs2) lb
                 | Unmodeled => True end))
    as [L HL].
  { intros [x m1 evs1|] _; [|exists []; auto].
    destruct (Hk x i m1) as [lb Hlb]; exists lb; auto. }
  exists (Unmodeled :: flat_map (fun o => match o with
      | Ok _ _ evs1 => map (fun o' => match o' with
          | Ok y m2 evs2 => Ok y m2 (evs1 ++ evs2) | Unmodeled => Unmodeled end) L
      | Unmodeled => [] end) l).
  unfold bind, Sys_Monad; intros [y m2 evs|] Ho; [|now left].
  destruct Ho as (x & m1 & evs1 & evs2 & H1 & H2 & ->); right.
  apply in_flat_map; exists (Ok x m1 evs1); split; [auto|].
  destruct (HL _ (Hl _ H1)) as (lb & Hlb & Hinc).
  apply (in_map (fun o' => match o' with
      | Ok y m2 evs2 => Ok y m2 (evs1 ++ evs2) | Unmodeled => Unmodeled end) L (Ok y m2 evs2)).
  apply Hinc, Hlb, H2.
Qed.

Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.

(** A byte-list [choose] is finite when one conjunct of its predicate bounds
    the length: an explicit [Z.of_nat (length bs) <= _]/[< _]/[= _], or a
    boolean well-formedness check whose first conjunct is
    [Nat.eqb (length bs) N] ([stat_buf_wf], [rlim64_wf], [utsname_wf],
    [nanosleep_rem_ok_b], [realtime_ok_b], [cputime_ok_b], [timespec_ok_b],
    [timeval_ok_b]). *)
Ltac len_bound :=
  lazymatch goal with
  | |- (Z.of_nat (length ?x) <= _)%Z =>
      first [ eassumption
            | apply Z.lt_le_incl; eassumption
            | apply Z.eq_le_incl; eassumption
            | match goal with
              | H : ?f x = true |- _ =>
                  let h := head_of f in unfold h in H;
                  repeat (apply andb_prop in H; destruct H as [H _]);
                  apply Nat.eqb_eq in H; rewrite H; apply Z.le_refl
              | H : ?f x _ = true |- _ =>
                  let h := head_of f in unfold h in H;
                  repeat (apply andb_prop in H; destruct H as [H _]);
                  apply Nat.eqb_eq in H; rewrite H; apply Z.le_refl
              end ]
  end.

Ltac scrut_of t := lazymatch t with match ?y with _ => _ end => scrut_of y | _ => t end.

Ltac fin_pred_auto :=
  first [ apply fin_pred_False | apply fin_pred_In | apply fin_pred_finite
        | eapply fin_pred_sub; [ | apply fin_pred_len_leZ ];
          intros ?x ?H; cbv beta in H; decompose [and] H; cbv beta; len_bound ].
Ltac fin_step :=
  lazymatch goal with
  | |- fin_sys (bind _ _)     => apply fin_bind; [ | intros ? ]
  | |- fin_sys (alt _ _)      => apply fin_alt
  | |- fin_sys (choose _)     => apply fin_choose; try fin_pred_auto
  | |- fin_sys (pure _)       => apply fin_pure
  | |- fin_sys unmodeled      => apply fin_unmodeled
  | |- fin_sys (emit _)       => apply fin_emit
  | |- fin_sys input          => apply fin_input
  | |- fin_sys sysno          => apply fin_sysno
  | |- fin_sys (arg _)        => apply fin_arg
  | |- fin_sys get_model      => apply fin_get_model
  | |- fin_sys get_fds        => apply fin_get_fds
  | |- fin_sys get_vmmaps     => apply fin_get_vmmaps
  | |- fin_sys (modify _)     => apply fin_modify
  | |- fin_sys (if ?b then _ else _)      => destruct b
  | |- fin_sys (match ?x with _ => _ end) => first [ progress cbv beta | let y := scrut_of x in destruct y ]
  | |- fin_sys (let x := _ in _)          => cbv zeta
  | |- fin_sys ?f     => let h := head_of f in unfold h
  end.
Ltac fin_arm := repeat fin_step.

(** ** One lemma per arm of [spec_table] *)

Lemma fin_getcwd size : fin_sys (getcwd_spec size).
Proof. fin_arm. Qed.

Lemma fin_eventfd2 flags : fin_sys (eventfd2_spec flags).
Proof. fin_arm. Qed.

Lemma fin_epoll_create1 flags32 : fin_sys (epoll_create1_spec flags32).
Proof. fin_arm. Qed.

Lemma fin_epoll_ctl epfd op32 tfd event : fin_sys (epoll_ctl_spec epfd op32 tfd event).
Proof. fin_arm. Qed.

Lemma fin_epoll_pwait epfd events maxevents32 sigmask sigsetsize : fin_sys (epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize).
Proof. fin_arm. Qed.

Lemma fin_dup oldfd : fin_sys (dup_spec oldfd).
Proof. fin_arm. Qed.

Lemma fin_dup3 oldfd newfd flags : fin_sys (dup3_spec oldfd newfd flags).
Proof. fin_arm. Qed.

Lemma fin_fcntl fd cmd arg : fin_sys (fcntl_spec fd cmd arg).
Proof. fin_arm. Qed.

Lemma fin_ioctl fd req : fin_sys (ioctl_spec fd req).
Proof. fin_arm. Qed.

Lemma fin_flock fd cmd : fin_sys (flock_spec fd cmd).
Proof. fin_arm. Qed.

Lemma fin_unlinkat dirfd pathp flags : fin_sys (unlinkat_spec dirfd pathp flags).
Proof. fin_arm. Qed.

Lemma fin_ftruncate fd len : fin_sys (ftruncate_spec fd len).
Proof. fin_arm. Qed.

Lemma fin_faccessat dirfd pathp mode : fin_sys (faccessat_spec dirfd pathp mode).
Proof. fin_arm. Qed.

Lemma fin_openat dirfd pathp flags : fin_sys (openat_spec dirfd pathp flags).
Proof. fin_arm. Qed.

Lemma fin_close fd : fin_sys (close_spec fd).
Proof. fin_arm. Qed.

Lemma fin_pipe2 fildes flags : fin_sys (pipe2_spec fildes flags).
Proof. fin_arm. Qed.

Lemma fin_getdents64 fd count : fin_sys (getdents64_spec fd count).
Proof. fin_arm. Qed.

Lemma fin_lseek fd off whence : fin_sys (lseek_spec fd off whence).
Proof. fin_arm. Qed.

Lemma fin_read fd buf count : fin_sys (read_spec fd buf count).
Proof. fin_arm. Qed.

Lemma fin_write fd buf count : fin_sys (write_spec fd buf count).
Proof. fin_arm. Qed.

Lemma fin_readv fd iov iovcnt : fin_sys (readv_spec fd iov iovcnt).
Proof. fin_arm. Qed.

Lemma fin_writev fd iov iovcnt : fin_sys (writev_spec fd iov iovcnt).
Proof. fin_arm. Qed.

Lemma fin_pread64 fd buf count pos : fin_sys (pread64_spec fd buf count pos).
Proof. fin_arm. Qed.

Lemma fin_pwrite64 fd buf count pos : fin_sys (pwrite64_spec fd buf count pos).
Proof. fin_arm. Qed.

Lemma fin_pselect6 n32 inp outp exp tsp sig : fin_sys (pselect6_spec n32 inp outp exp tsp sig).
Proof. fin_arm. Qed.

Lemma fin_ppoll ufds nfds tsp sig sigsetsize : fin_sys (ppoll_spec ufds nfds tsp sig sigsetsize).
Proof. fin_arm. Qed.

Lemma fin_readlinkat dirfd : fin_sys (readlinkat_spec dirfd).
Proof. fin_arm. Qed.

Lemma fin_newfstatat dirfd pathp flag : fin_sys (newfstatat_spec dirfd pathp flag).
Proof. fin_arm. Qed.

Lemma fin_fstat fd statbuf : fin_sys (fstat_spec fd statbuf).
Proof. fin_arm. Qed.

Lemma fin_fsync fd : fin_sys (fsync_spec fd).
Proof. fin_arm. Qed.

Lemma fin_timerfd_create clkid flags : fin_sys (timerfd_create_spec clkid flags).
Proof. fin_arm. Qed.

Lemma fin_exit code : fin_sys (exit_spec code).
Proof. fin_arm. Qed.

Lemma fin_set_tid_address : fin_sys set_tid_address_spec.
Proof. fin_arm. Qed.

Lemma fin_futex uaddr op val utime : fin_sys (futex_spec uaddr op val utime).
Proof. fin_arm. Qed.

Lemma fin_nanosleep rqtp rmtp : fin_sys (nanosleep_spec rqtp rmtp).
Proof. fin_arm. Qed.

Lemma fin_clock_gettime clkid tp : fin_sys (clock_gettime_spec clkid tp).
Proof. fin_arm. Qed.

Lemma fin_sched_setscheduler pid policy param : fin_sys (sched_setscheduler_spec pid policy param).
Proof. fin_arm. Qed.

Lemma fin_sched_getaffinity len : fin_sys (sched_getaffinity_spec len).
Proof. fin_arm. Qed.

Lemma fin_sched_yield : fin_sys sched_yield_spec.
Proof. fin_arm. Qed.

Lemma fin_tkill pid sig : fin_sys (tkill_spec pid sig).
Proof. fin_arm. Qed.

Lemma fin_tgkill tgid pid sig : fin_sys (tgkill_spec tgid pid sig).
Proof. fin_arm. Qed.

Lemma fin_sigaltstack uss uoss : fin_sys (sigaltstack_spec uss uoss).
Proof. fin_arm. Qed.

Lemma fin_rt_sigaction sig act oact ss : fin_sys (rt_sigaction_spec sig act oact ss).
Proof. fin_arm. Qed.

Lemma fin_rt_sigprocmask how nset oset ss : fin_sys (rt_sigprocmask_spec how nset oset ss).
Proof. fin_arm. Qed.

Lemma fin_setid get put user v : fin_sys (setid_spec get put user v).
Proof. fin_arm. Qed.

Lemma fin_setresid get put user r e s : fin_sys (setresid_spec get put user r e s).
Proof. fin_arm. Qed.

Lemma fin_setsid : fin_sys setsid_spec.
Proof. fin_arm. Qed.

Lemma fin_getgroups gidsetsize : fin_sys (getgroups_spec gidsetsize).
Proof. fin_arm. Qed.

Lemma fin_setgroups : fin_sys setgroups_spec.
Proof. fin_arm. Qed.

Lemma fin_uname name : fin_sys (uname_spec name).
Proof. fin_arm. Qed.

Lemma fin_prctl option_ arg2 : fin_sys (prctl_spec option_ arg2).
Proof. fin_arm. Qed.

Lemma fin_gettimeofday tv tz : fin_sys (gettimeofday_spec tv tz).
Proof. fin_arm. Qed.

Lemma fin_getpid : fin_sys getpid_spec.
Proof. fin_arm. Qed.

Lemma fin_getid sel : fin_sys (getid_spec sel).
Proof. fin_arm. Qed.

Lemma fin_gettid : fin_sys gettid_spec.
Proof. fin_arm. Qed.

Lemma fin_socket domain type protocol : fin_sys (socket_spec domain type protocol).
Proof. fin_arm. Qed.

Lemma fin_socketpair family type protocol sv : fin_sys (socketpair_spec family type protocol sv).
Proof. fin_arm. Qed.

Lemma fin_bind_syscall fd addrp addrlen : fin_sys (bind_spec fd addrp addrlen).
Proof. fin_arm. Qed.

Lemma fin_listen fd backlog : fin_sys (listen_spec fd backlog).
Proof. fin_arm. Qed.

Lemma fin_accept4 fd addrp addrlenp flags : fin_sys (accept4_spec fd addrp addrlenp flags).
Proof. fin_arm. Qed.

Lemma fin_connect fd addrp addrlen : fin_sys (connect_spec fd addrp addrlen).
Proof. fin_arm. Qed.

Lemma fin_getsockname fd : fin_sys (getsockname_spec fd).
Proof. fin_arm. Qed.

Lemma fin_getpeername fd : fin_sys (getpeername_spec fd).
Proof. fin_arm. Qed.

Lemma fin_sendto fd buf count flags addrp addrlen : fin_sys (sendto_spec fd buf count flags addrp addrlen).
Proof. fin_arm. Qed.

Lemma fin_recvfrom fd buf size : fin_sys (recvfrom_spec fd buf size).
Proof. fin_arm. Qed.

Lemma fin_setsockopt fd level optlen : fin_sys (setsockopt_spec fd level optlen).
Proof. fin_arm. Qed.

Lemma fin_getsockopt fd level optlenp : fin_sys (getsockopt_spec fd level optlenp).
Proof. fin_arm. Qed.

Lemma fin_shutdown fd how : fin_sys (shutdown_spec fd how).
Proof. fin_arm. Qed.

Lemma fin_sendmsg fd msgp flags : fin_sys (sendmsg_spec fd msgp flags).
Proof. fin_arm. Qed.

Lemma fin_recvmsg fd flags : fin_sys (recvmsg_spec fd flags).
Proof. fin_arm. Qed.

Lemma fin_brk req : fin_sys (brk_spec req).
Proof. fin_arm. Qed.

Lemma fin_munmap addr len : fin_sys (munmap_spec addr len).
Proof. fin_arm. Qed.

Lemma fin_mremap old old_size new_size flags : fin_sys (mremap_spec old old_size new_size flags).
Proof. fin_arm. Qed.

Lemma fin_clone flags : fin_sys (clone_spec flags).
Proof. fin_arm. Qed.

Lemma fin_mmap addr len prot flags fd off : fin_sys (mmap_spec addr len prot flags fd off).
Proof. fin_arm. Qed.

Lemma fin_mprotect addr len prot : fin_sys (mprotect_spec addr len prot).
Proof. fin_arm. Qed.

Lemma fin_madvise addr len advice : fin_sys (madvise_spec addr len advice).
Proof. fin_arm. Qed.

Lemma fin_wait4 upid stat_addr options rusage : fin_sys (wait4_spec upid stat_addr options rusage).
Proof. fin_arm. Qed.

Lemma fin_prlimit64 pid resource new_rlim old_rlim : fin_sys (prlimit64_spec pid resource new_rlim old_rlim).
Proof. fin_arm. Qed.

Lemma fin_getrandom buf buflen flags : fin_sys (getrandom_spec buf buflen flags).
Proof. fin_arm. Qed.

Lemma fin_clone3 uargs size : fin_sys (clone3_spec uargs size).
Proof. fin_arm. Qed.

Lemma fin_faccessat2 dirfd pathp mode flags : fin_sys (faccessat2_spec dirfd pathp mode flags).
Proof. fin_arm. Qed.

Create HintDb fin.
#[local] Hint Resolve
  fin_getcwd
  fin_eventfd2
  fin_epoll_create1
  fin_epoll_ctl
  fin_epoll_pwait
  fin_dup
  fin_dup3
  fin_fcntl
  fin_ioctl
  fin_flock
  fin_unlinkat
  fin_ftruncate
  fin_faccessat
  fin_openat
  fin_close
  fin_pipe2
  fin_getdents64
  fin_lseek
  fin_read
  fin_write
  fin_readv
  fin_writev
  fin_pread64
  fin_pwrite64
  fin_pselect6
  fin_ppoll
  fin_readlinkat
  fin_newfstatat
  fin_fstat
  fin_fsync
  fin_timerfd_create
  fin_exit
  fin_set_tid_address
  fin_futex
  fin_nanosleep
  fin_clock_gettime
  fin_sched_setscheduler
  fin_sched_getaffinity
  fin_sched_yield
  fin_tkill
  fin_tgkill
  fin_sigaltstack
  fin_rt_sigaction
  fin_rt_sigprocmask
  fin_setid
  fin_setresid
  fin_setsid
  fin_getgroups
  fin_setgroups
  fin_uname
  fin_prctl
  fin_gettimeofday
  fin_getpid
  fin_getid
  fin_gettid
  fin_socket
  fin_socketpair
  fin_bind_syscall
  fin_listen
  fin_accept4
  fin_connect
  fin_getsockname
  fin_getpeername
  fin_sendto
  fin_recvfrom
  fin_setsockopt
  fin_getsockopt
  fin_shutdown
  fin_sendmsg
  fin_recvmsg
  fin_brk
  fin_munmap
  fin_mremap
  fin_clone
  fin_mmap
  fin_mprotect
  fin_madvise
  fin_wait4
  fin_prlimit64
  fin_getrandom
  fin_clone3
  fin_faccessat2
  : fin.

(** Every arm of the table admits finitely many outcomes.  A new arm whose
    spec has no [fin_<syscall>] lemma leaves an unsolved goal here. *)
Theorem spec_table_finite : Forall (fun a => fin_sys (sa_spec a)) spec_table.
Proof.
  unfold spec_table; repeat apply Forall_cons; try apply Forall_nil;
    cbn [sa_spec]; intros i m;
    lazymatch goal with |- exists l, forall o, ?c i m o -> _ =>
      enough (fin_sys c) as H by apply H end;
    auto with fin.
Qed.

Lemma lookup_arm_In t n a : lookup_arm t n = Some a -> In a t.
Proof.
  induction t as [|b t IH]; cbn; [discriminate|].
  destruct (Z.eqb (sa_no b) n); [injection 1 as ->; now left | right; auto].
Qed.

(** [syscall_spec] is finitely branching: every input and model admit
    finitely many outcomes. *)
Theorem syscall_spec_finite : forall i m,
  exists l : list (outcome SyscallEffect), forall o, syscall_spec i m o -> In o l.
Proof.
  intros i m; unfold syscall_spec, dispatch.
  destruct (lookup_arm spec_table (bv_unsigned (in_sysno i))) as [a|] eqn:E.
  - apply lookup_arm_In in E.
    exact (proj1 (Forall_forall _ _) spec_table_finite a E i m).
  - exists [Unmodeled]; unfold unmodeled; intros o ->; now left.
Qed.
