

namespace AgentKernel.Replay

/-! ## Per-kind payload record types — concrete `Nat` carriers -/


structure CapMintRecord where
  mintedCapId : Nat
  deriving DecidableEq


structure RetractRecord where
  retractTarget : Nat
  deriving DecidableEq


structure PlanRecord where
  linkedExecId : Nat
  deriving DecidableEq


structure RefusalRecord where
  refusalReasonCode : Nat
  deriving DecidableEq


structure ViolationRecord where
  violationContractId : Nat
  deriving DecidableEq


structure ContractRegisterRecord where
  registeredContractId : Nat
  deriving DecidableEq


structure HumanGateRecord where
  policyId        : Nat
  decisionOutcome : Bool
  deriving DecidableEq




inductive FailureMode : Type
  /-- Recoverable failure (retry-allowed). -/
  | transient
  /-- Non-recoverable failure (retry-prohibited). -/
  | permanent
  /-- Adversarial / corrupted-state failure (incident-trigger). -/
  | byzantine
  deriving DecidableEq, Repr, Inhabited


structure FailureRecord where
  mode : FailureMode
  deriving DecidableEq


structure EnvDigestRecord where
  digest : Nat
  deriving DecidableEq



/-- Kind-discriminated payload sum. Closed alphabet at v1.8 :
    10 constructors (`base` + 6 kind-specific from  + 2 
    additions: `humanGate` + `failureMode`; + 1  cross-kind
    addition: `envBinding`). -/
inductive EventPayload : Type
  /-- No kind-specific payload (deterministic kinds without
      side-table; all NonDetKinds at ). -/
  | base : EventPayload
  
  | cap_mint : CapMintRecord → EventPayload
  
  | retract : RetractRecord → EventPayload
  
  | plan : PlanRecord → EventPayload
  
  | refusal : RefusalRecord → EventPayload
  
  | contractViolation : ViolationRecord → EventPayload
  
  | contractRegister : ContractRegisterRecord → EventPayload
  
  | humanGate : HumanGateRecord → EventPayload
  
  | failureMode : FailureRecord → EventPayload
  
  | envBinding : EnvDigestRecord → EventPayload
  deriving DecidableEq

/-- Default payload for record-update / default-value sites.
    Equivalent to `EventPayload.base`; preserves the v1.7
    default-`none` discipline shape at the structure level. -/
@[inline] def EventPayload.default : EventPayload := EventPayload.base

instance : Inhabited EventPayload := ⟨EventPayload.base⟩


instance : Repr EventPayload where
  reprPrec p _ := match p with
    | .base                => "EventPayload.base"
    | .cap_mint _          => "EventPayload.cap_mint⟨..⟩"
    | .retract _           => "EventPayload.retract⟨..⟩"
    | .plan _              => "EventPayload.plan⟨..⟩"
    | .refusal _           => "EventPayload.refusal⟨..⟩"
    | .contractViolation _ => "EventPayload.contractViolation⟨..⟩"
    | .contractRegister _  => "EventPayload.contractRegister⟨..⟩"
    | .humanGate _         => "EventPayload.humanGate⟨..⟩"
    | .failureMode _       => "EventPayload.failureMode⟨..⟩"
    | .envBinding _        => "EventPayload.envBinding⟨..⟩"

end AgentKernel.Replay
