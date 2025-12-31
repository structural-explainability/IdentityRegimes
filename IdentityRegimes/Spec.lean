import IdentityRegimes.Core

namespace IdentityRegimes.Spec

/-!
REQ:
  Spec surface for IdentityRegimes (IR): stable identifiers and requirement-shaped Props.

WHY:
  This repo is a foundational proof repo. The "REQ_*" definitions here are
  traceability surfaces: they name the proposition-shapes that the Core file
  proves (or assumes), without depending on `open` or namespace accidents.

OBS:
  We fully qualify Core names to prevent scope breakage.
-/



-- ============================================================================
-- Stable identifier strings (traceability only)
-- ============================================================================

def IR_AXIOM_NON_COLLAPSE : String := "IR.AXIOM.NON_COLLAPSE"
def IR_REQUIREMENTS_CARDINALITY_SIX : String := "IR.REQUIREMENTS.CARDINALITY.SIX"
def IR_THEOREM_NECESSITY : String := "IR.THEOREM.NECESSITY"
def IR_THEOREM_SUFFICIENCY : String := "IR.THEOREM.SUFFICIENCY"
def IR_THEOREM_MAIN : String := "IR.THEOREM.MAIN"

-- ============================================================================
-- Requirement-shaped Props (traceability-to-Lean surface)
-- ============================================================================

/-- REQ: IR.AXIOM.NON_COLLAPSE -/
def Req_IR_AXIOM_NON_COLLAPSE
  {Regime : Type} [DecidableEq Regime]
  (satisfies : Regime -> IdentityRegimes.Core.Requirement -> Prop) : Prop :=
  ∀ (r : Regime)
    (req1 req2 : IdentityRegimes.Core.Requirement),
      satisfies r req1 -> satisfies r req2 -> req1 = req2

/-- REQ: IR.REQUIREMENTS.CARDINALITY.SIX -/
def Req_IR_REQUIREMENTS_CARDINALITY_SIX : Prop :=
  Fintype.card IdentityRegimes.Core.Requirement = 6

/-- REQ: IR.THEOREM.NECESSITY -/
def Req_IR_THEOREM_NECESSITY
  {Regime : Type} [DecidableEq Regime]
  (satisfies : Regime -> IdentityRegimes.Core.Requirement -> Prop)
  (S : IdentityRegimes.Core.Substrate Regime) : Prop :=
  IdentityRegimes.Core.Substrate.satisfiesAll satisfies S -> S.card >= 6

/-- REQ: IR.THEOREM.SUFFICIENCY -/
def Req_IR_THEOREM_SUFFICIENCY : Prop :=
  ∃ S : IdentityRegimes.Core.Substrate IdentityRegimes.Core.CanonicalRegime,
    S.card = 6 ∧
    IdentityRegimes.Core.Substrate.satisfiesAll IdentityRegimes.Core.canonicalSatisfies S

/-- REQ: IR.THEOREM.MAIN -/
def Req_IR_THEOREM_MAIN
  {Regime : Type} [DecidableEq Regime] : Prop :=
  (∀ (satisfies : Regime -> IdentityRegimes.Core.Requirement -> Prop)
     (S : IdentityRegimes.Core.Substrate Regime),
      IdentityRegimes.Core.Substrate.satisfiesAll satisfies S -> S.card >= 6)
  ∧
  (∃ S : IdentityRegimes.Core.Substrate IdentityRegimes.Core.CanonicalRegime,
     S.card = 6 ∧
     IdentityRegimes.Core.Substrate.satisfiesAll IdentityRegimes.Core.canonicalSatisfies S)

end IdentityRegimes.Spec
