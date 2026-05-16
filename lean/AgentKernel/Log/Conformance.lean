import AgentKernel.Log



namespace AgentKernel.Log.Conformance

abbrev Bytes : Type := List UInt8
abbrev Hash  : Type := UInt64

def genesis : Bytes := []

@[inline] def fnv1aStep (h : UInt64) (b : UInt8) : UInt64 :=
  (h ^^^ b.toUInt64) * (1099511628211 : UInt64)

def H : Bytes → Hash :=
  List.foldl fnv1aStep (14695981039346656037 : UInt64)

@[inline] def hashToBytes (h : UInt64) : List UInt8 :=
  [ (h.shiftRight  0).toUInt8
  , (h.shiftRight  8).toUInt8
  , (h.shiftRight 16).toUInt8
  , (h.shiftRight 24).toUInt8
  , (h.shiftRight 32).toUInt8
  , (h.shiftRight 40).toUInt8
  , (h.shiftRight 48).toUInt8
  , (h.shiftRight 56).toUInt8 ]

def serialize (h : Hash) (b : Bytes) : Bytes :=
  hashToBytes h ++ b

abbrev ConcreteChain := LogChain Bytes Hash

/-- Kernel emit: append an entry whose `prev` field equals the
    current chain's root. Mirrors `Append` in `Log.tla`'s `Next_M6`. -/
def emit_append (chain : ConcreteChain) (payload : Bytes) : ConcreteChain :=
  chain ++ [{ prev    := chain.root H genesis serialize
            , payload := payload }]


theorem wellFormed_emit_append
    (chain : ConcreteChain) (payload : Bytes)
    (h : chain.wellFormed H genesis serialize) :
    (emit_append chain payload).wellFormed H genesis serialize := by
  unfold emit_append
  exact LogChain.wellFormed_append_singleton
    H genesis serialize chain
    { prev := chain.root H genesis serialize, payload := payload }
    h rfl

/-- Empty chain is wellFormed by definition. -/
theorem wellFormed_empty :
    LogChain.wellFormed H genesis serialize ([] : ConcreteChain) :=
  LogChain.wellFormed_nil H genesis serialize

/-- Convenience constructor: the singleton kernel-emitted chain. -/
def demoChain (payload : Bytes) : ConcreteChain :=
  emit_append [] payload

/-- T4 instantiates on a kernel-emitted chain. The trivial left-disjunct
    case (chains identical) suffices to demonstrate that all hypotheses
    of `t4_audit_integrity` discharge cleanly on the concrete instance. -/
theorem t4_demo (payload : Bytes) :
    demoChain payload = demoChain payload ∨
    ∃ (a a' : Hash) (b b' : Bytes),
      (a, b) ≠ (a', b') ∧ H (serialize a b) = H (serialize a' b') := by
  have hWf : (demoChain payload).wellFormed H genesis serialize :=
    wellFormed_emit_append [] payload wellFormed_empty
  exact t4_audit_integrity H genesis serialize
    (demoChain payload) (demoChain payload)
    rfl hWf hWf rfl

end AgentKernel.Log.Conformance

#print axioms AgentKernel.Log.Conformance.wellFormed_emit_append
#print axioms AgentKernel.Log.Conformance.t4_demo
