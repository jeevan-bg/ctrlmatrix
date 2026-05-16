------------------------------ MODULE Liveness ------------------------------


EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Delta_ext,      \* Nat; externalization deadline; > 0
    Delta_rev,      \* Nat; revocation deadline; > 0;
    Delta_cmp,      \* Nat; commit-or-compensate deadline; > 0
    MaxNow,         \* Nat; TLC bound on `now` clock progression
    MaxPending,     \* Nat; TLC bound on pending-set cardinality
    Partition_P     \* Nat; bound on partition-window length;

ASSUME ConstantsAssumption ==
    /\ Delta_ext   \in Nat
    /\ Delta_rev   \in Nat
    /\ Delta_cmp   \in Nat
    /\ MaxNow      \in Nat
    /\ MaxPending  \in Nat
    /\ Partition_P \in Nat
    /\ Delta_ext   > 0
    /\ Delta_rev   > 0
    /\ Delta_cmp   > 0

VARIABLES
    now,            \* Nat; discrete clock
    pendingExt,     \* SUBSET (Nat \X Nat); (request_id, request_time) pairs
                    \*   for outstanding externalize requests
    pendingRev,     \* SUBSET (Nat \X Nat); same shape, for revoke
    pendingCmp,     \* SUBSET (Nat \X Nat); same shape, for commit-or-compensate
    partitionActive,\* BOOLEAN; TRUE iff a partition is currently active.
                    \*   Encoded as a separate flag because TLA+ has no
                    \*   native option type and unary minus on Nat for a
                    \*   sentinel value would not type-check.
    partitionStart  \* Nat; the time the current partition began (only
                    \*   meaningful when partitionActive = TRUE).
                    \*   Used to bound SF-under-partition for L_Rev.

vars == <<now, pendingExt, pendingRev, pendingCmp,
          partitionActive, partitionStart>>

(******************************************************************************
  Helpers
 *****************************************************************************)

PendingIds(P) == { p[1] : p \in P }

Partitioned == partitionActive

(******************************************************************************
  Initial state
 *****************************************************************************)

Init ==
    /\ now             = 0
    /\ pendingExt      = {}
    /\ pendingRev      = {}
    /\ pendingCmp      = {}
    /\ partitionActive = FALSE
    /\ partitionStart  = 0

(******************************************************************************
  Type invariant (bounded for TLC)
 *****************************************************************************)

TypeOK ==
    /\ now \in 0 .. MaxNow
    /\ pendingExt \subseteq ((0 .. MaxNow) \X (0 .. MaxNow))
    /\ pendingRev \subseteq ((0 .. MaxNow) \X (0 .. MaxNow))
    /\ pendingCmp \subseteq ((0 .. MaxNow) \X (0 .. MaxNow))
    /\ Cardinality(pendingExt) <= MaxPending
    /\ Cardinality(pendingRev) <= MaxPending
    /\ Cardinality(pendingCmp) <= MaxPending
    /\ partitionActive \in BOOLEAN
    /\ partitionStart \in 0 .. MaxNow

(******************************************************************************
  Externalization actions (L_Ext clock model)
 *****************************************************************************)

RequestExt(id) ==
    /\ id \in 0 .. MaxNow
    /\ id \notin PendingIds(pendingExt)
    /\ Cardinality(pendingExt) < MaxPending
    /\ pendingExt' = pendingExt \cup {<<id, now>>}
    /\ UNCHANGED <<now, pendingRev, pendingCmp,
                   partitionActive, partitionStart>>

Externalize ==
    /\ pendingExt # {}
    /\ \E p \in pendingExt :
         pendingExt' = pendingExt \ {p}
    /\ UNCHANGED <<now, pendingRev, pendingCmp,
                   partitionActive, partitionStart>>

(******************************************************************************
  Revocation actions (L_Rev clock model; SF under bounded partition)
 *****************************************************************************)

RequestRev(id) ==
    /\ id \in 0 .. MaxNow
    /\ id \notin PendingIds(pendingRev)
    /\ Cardinality(pendingRev) < MaxPending
    /\ pendingRev' = pendingRev \cup {<<id, now>>}
    /\ UNCHANGED <<now, pendingExt, pendingCmp,
                   partitionActive, partitionStart>>

Revoke ==
    /\ ~Partitioned                 \* SF only fires outside partition
    /\ pendingRev # {}
    /\ \E p \in pendingRev :
         pendingRev' = pendingRev \ {p}
    /\ UNCHANGED <<now, pendingExt, pendingCmp,
                   partitionActive, partitionStart>>

(******************************************************************************
  Commit-or-compensate actions (L_Cmp clock model)
 *****************************************************************************)

RequestCmp(id) ==
    /\ id \in 0 .. MaxNow
    /\ id \notin PendingIds(pendingCmp)
    /\ Cardinality(pendingCmp) < MaxPending
    /\ pendingCmp' = pendingCmp \cup {<<id, now>>}
    /\ UNCHANGED <<now, pendingExt, pendingRev,
                   partitionActive, partitionStart>>

\* Commit and Compensate are observationally identical at L0 -- both
\* discharge a pending request. L1+ refines this into separate paths.
CommitOrCompensate ==
    /\ pendingCmp # {}
    /\ \E p \in pendingCmp :
         pendingCmp' = pendingCmp \ {p}
    /\ UNCHANGED <<now, pendingExt, pendingRev,
                   partitionActive, partitionStart>>



DeadlineBudgetOk(t1) ==
    /\ \A p \in pendingExt : t1 <= p[2] + Delta_ext
    /\ \A p \in pendingRev : t1 <= p[2] + Delta_rev
    /\ \A p \in pendingCmp : t1 <= p[2] + Delta_cmp

\* PartitionBudgetOk: Tick can only advance past partitionStart by
\* Partition_P ticks. When the partition is at its bound, Tick is
\* disabled and EndPartition is the only action that can fire,
\* forcing it under WF.
PartitionBudgetOk(t1) ==
    Partitioned => (t1 - partitionStart <= Partition_P)

Tick ==
    /\ now < MaxNow
    /\ DeadlineBudgetOk(now + 1)
    /\ PartitionBudgetOk(now + 1)
    /\ now' = now + 1
    /\ UNCHANGED <<pendingExt, pendingRev, pendingCmp,
                   partitionActive, partitionStart>>



BeginPartition ==
    /\ ~Partitioned
    /\ partitionActive' = TRUE
    /\ partitionStart'  = now
    /\ UNCHANGED <<now, pendingExt, pendingRev, pendingCmp>>

\* EndPartition: closes any active partition. Bounded above by
\* , vacuous-SF trap). No lower bound: a 0-duration
\* partition is degenerate but not blocking. Critically, EndPartition
\* must be enabled even when Tick is disabled (deadline-budget
\* exhausted while partitioned), otherwise the spec deadlocks; this
\* is why EndPartition does NOT depend on Tick having advanced
\* `now`.
EndPartition ==
    /\ Partitioned
    /\ now - partitionStart <= Partition_P
    /\ partitionActive' = FALSE
    /\ partitionStart'  = 0
    /\ UNCHANGED <<now, pendingExt, pendingRev, pendingCmp>>

(******************************************************************************
  Composite next-state relation
 *****************************************************************************)

Next ==
    \/ \E id \in 0 .. MaxNow : RequestExt(id)
    \/ Externalize
    \/ \E id \in 0 .. MaxNow : RequestRev(id)
    \/ Revoke
    \/ \E id \in 0 .. MaxNow : RequestCmp(id)
    \/ CommitOrCompensate
    \/ Tick
    \/ BeginPartition
    \/ EndPartition



Fairness ==
    /\ WF_vars(Externalize)
    /\ SF_vars(Revoke)
    /\ WF_vars(CommitOrCompensate)
    /\ WF_vars(Tick)
    /\ WF_vars(EndPartition)

Spec_Liveness == Init /\ [][Next]_vars /\ Fairness



\* L_Ext: every externalize request is eventually consumed.
\* (Sanity form; entailed by L_Ext_Bound when Delta_ext is finite.)
L_Ext ==
    \A id \in 0 .. MaxNow :
        (id \in PendingIds(pendingExt)) ~> (id \notin PendingIds(pendingExt))

\* L_Ext_Bound: every externalize request submitted at t0 is consumed
\* with `now <= t0 + Delta_ext`. THIS IS THE LOAD-BEARING FORM.
L_Ext_Bound ==
    \A id \in 0 .. MaxNow : \A t0 \in 0 .. MaxNow :
        (<<id, t0>> \in pendingExt)
            ~> (id \notin PendingIds(pendingExt) /\ now <= t0 + Delta_ext)

\* L_Rev: every revoke request is eventually consumed (sanity form).
L_Rev ==
    \A id \in 0 .. MaxNow :
        (id \in PendingIds(pendingRev)) ~> (id \notin PendingIds(pendingRev))

\* L_Rev_Bound: every revoke request submitted at t0 is consumed with
\* Delta_rev is the first-class L0 parameter the deployment SLA pins.
\*
\* Strong-fairness-under-partition: SF_vars(Revoke) requires that if
\* Revoke is enabled infinitely often it eventually fires. The
\* `~Partitioned` precondition on Revoke combined with the bounded
\* Partition_P + WF on EndPartition guarantees Revoke is enabled
\* infinitely often even if partitions occur intermittently.
L_Rev_Bound ==
    \A id \in 0 .. MaxNow : \A t0 \in 0 .. MaxNow :
        (<<id, t0>> \in pendingRev)
            ~> (id \notin PendingIds(pendingRev) /\ now <= t0 + Delta_rev)

\* L_Cmp: every commit-or-compensate request is eventually consumed.
L_Cmp ==
    \A id \in 0 .. MaxNow :
        (id \in PendingIds(pendingCmp)) ~> (id \notin PendingIds(pendingCmp))

\* L_Cmp_Bound: every commit-or-compensate request submitted at t0 is
\* consumed with `now <= t0 + Delta_cmp`.
L_Cmp_Bound ==
    \A id \in 0 .. MaxNow : \A t0 \in 0 .. MaxNow :
        (<<id, t0>> \in pendingCmp)
            ~> (id \notin PendingIds(pendingCmp) /\ now <= t0 + Delta_cmp)



THEOREM Thm_L_Ext_Bound  == Spec_Liveness => L_Ext_Bound  (* TLC-checked *)
THEOREM Thm_L_Rev_Bound  == Spec_Liveness => L_Rev_Bound  
THEOREM Thm_L_Cmp_Bound  == Spec_Liveness => L_Cmp_Bound  (* TLC-checked *)



(* --- Bounded-pending invariants (key safety properties) --- *)

Inv_BoundedExt ==
    \A p \in pendingExt : now <= p[2] + Delta_ext

Inv_BoundedRev ==
    \A p \in pendingRev : now <= p[2] + Delta_rev

Inv_BoundedCmp ==
    \A p \in pendingCmp : now <= p[2] + Delta_cmp



Inv_PartitionBudget ==
    Partitioned => (now - partitionStart) <= Partition_P

==============================================================================
