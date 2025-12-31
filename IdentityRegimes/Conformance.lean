import IdentityRegimes.Core
import IdentityRegimes.Spec

namespace IdentityRegimes.Conformance

/-!
REQ:
  Conformance evidence for the IdentityRegimes repo.

WHY:
  This is a foundational proof repo. "Conformance" here means:
  the repo provides the declared axiom + theorems in `IdentityRegimes.Core`.

OBS:
  We store proofs (and the axiom reference), not equivalences.
-/



open IdentityRegimes.Core
open IdentityRegimes.Spec

structure ConformanceEvidence where
  -- REQ: IR.REQUIREMENTS.CARDINALITY.SIX
  requirements_cardinality_six :
    Req_IR_REQUIREMENTS_CARDINALITY_SIX

  -- REQ: IR.THEOREM.NECESSITY
  theorem_necessity :
    ∀ {Regime : Type} [DecidableEq Regime],
      ∀ (satisfies : Regime -> Requirement -> Prop)
        (S : Substrate Regime),
        Req_IR_THEOREM_NECESSITY (Regime := Regime) satisfies S

  -- REQ: IR.THEOREM.SUFFICIENCY
  theorem_sufficiency :
    Req_IR_THEOREM_SUFFICIENCY

  -- REQ: IR.THEOREM.MAIN
  theorem_main :
    ∀ {Regime : Type} [DecidableEq Regime],
      Req_IR_THEOREM_MAIN (Regime := Regime)

-- Default witness evidence, discharged by Core artifacts.
def evidence : ConformanceEvidence :=
{ requirements_cardinality_six := by
    simpa [Req_IR_REQUIREMENTS_CARDINALITY_SIX] using IdentityRegimes.Core.requirement_count

, theorem_necessity := by
    intro Regime _ satisfies S h_all
    -- unfold the Req-shape and use the Core theorem
    simpa [Req_IR_THEOREM_NECESSITY] using
      (IdentityRegimes.Core.six_regimes_necessary (Regime := Regime) satisfies S) h_all

, theorem_sufficiency := by
    -- unfold the Req-shape and use the Core theorem
    simpa [Req_IR_THEOREM_SUFFICIENCY] using IdentityRegimes.Core.six_regimes_sufficient

, theorem_main := by
    intro Regime _
    -- unfold the Req-shape and use the Core theorem
    simpa [Req_IR_THEOREM_MAIN] using IdentityRegimes.Core.six_regimes_theorem (Regime := Regime)
}

end IdentityRegimes.Conformance
