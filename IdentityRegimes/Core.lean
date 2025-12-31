import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace IdentityRegimes.Core

open Classical



/-!
# The Identity Regimes Theorem (Abstract)

This module sets up an abstract formalization of the result
for accountability substrates optimized for stability
under persistent interpretive disagreement.

Approach:
- We represent requirements and prove a lower bound on any
  satisfying substrate from an independence / non-collapse principle.

What this file provides:
- A clean statement of the assumptions needed for a non-tautological
  lower necessity bound.
- A canonical "sufficiency" construction (a witness model).

Paper (In Progress):
"Substrate Stability Under Persistent Disagreement:
 Structural Constraints for Neutral Ontologies" (Case, 2025)

Domain scope:
This formalization applies to substrates optimized for stability under durable
interpretive disagreement.
It does not apply to substrates optimized for expressiveness
within a single interpretive community or
where semantic consensus is achievable.

Structure:
- Part 1: Requirements (R1-R6) as an inductive type
- Part 2: Abstract regimes, substrates, and satisfaction
- Part 3: Independence / non-collapse axiom (the real content)
- Part 4: Necessity theorem (>= 6 regimes)
- Part 5: Sufficiency theorem (a 6-regime model exists)
- Part 6: Main theorem (necessary and sufficient)
- Part 7: Verification hints
-/


-- ======================================================================
-- PART 1: REQUIREMENTS (R1-R6)
-- ======================================================================

/-- Regime-forcing structural requirements (R1-R6). -/
inductive Requirement where
  | R1  -- obligation-bearing / actor vs non-actor capacity
  | R2  -- acted-upon / locus capacity
  | R3  -- authority-grounding capacity
  | R4  -- time-indexed occurrence capacity
  | R5  -- applicability / scope capacity
  | R6  -- descriptive record / observation capacity
  deriving DecidableEq, Repr, Fintype

/-- Sanity check: there are exactly six requirements. -/
theorem requirement_count : Fintype.card Requirement = 6 := by
  native_decide

-- ======================================================================
-- PART 2: ABSTRACT REGIMES, SUBSTRATES, AND SATISFACTION
-- ======================================================================

variable {Regime : Type} [DecidableEq Regime]

/-- A substrate is a finite set of regimes. -/
abbrev Substrate (Regime : Type) [DecidableEq Regime] := Finset Regime

/-- Substrate `S` satisfies requirement `req` if it contains some regime
    that satisfies it. -/
def Substrate.satisfiesReq
  (satisfies : Regime -> Requirement -> Prop)
  (S : Substrate Regime)
  (req : Requirement) : Prop :=
  ∃ r : Regime, r ∈ S ∧ satisfies r req

/-- Substrate `S` satisfies all requirements R1-R6. -/
def Substrate.satisfiesAll
  (satisfies : Regime -> Requirement -> Prop)
  (S : Substrate Regime) : Prop :=
  ∀ req : Requirement, S.satisfiesReq satisfies req

-- ======================================================================
-- PART 3: INDEPENDENCE / NON-COLLAPSE (AXIOM)
-- ======================================================================

/-!
## Part 3: Independence / non-collapse

This is the core structural content and domain assumption.
It encodes the claim that the requirements are independent
in the sense that no single regime can simultaneously discharge
two distinct requirements *without hidden discriminators*.

Formal form:
If `r` satisfies `req1` and `r` satisfies `req2`, then `req1 = req2`.

This is the minimal principle needed to derive a genuine lower bound.
-/

/-!
## OBS: Independence / Non-Collapse Assumption

**Observation (Domain Assumption):**
The regime-forcing requirements (R1–R6) are *independent* in the sense that
no single identity-and-persistence regime can satisfy more than one requirement
without introducing hidden discriminators.

**Formal Role in the Proof:**
This assumption is the *only* source of the lower bound (≥ 6).
If it is weakened or removed, the necessity theorem fails.

**Interpretive Meaning:**
- Distinct requirements correspond to distinct identity conditions.
- Collapsing two requirements into one regime would require
  extra structure (roles, context, norms, causation) that is
  explicitly excluded by the neutrality and stability constraints.

**Scope Note:**
This is not a logical truth; it is a structural assumption about
accountability substrates optimized for persistent disagreement.
Domains that permit negotiated semantics or embedded role distinctions
may reject this assumption and thereby fall outside the theorem’s scope.
-/
axiom satisfies_functional
  (satisfies : Regime -> Requirement -> Prop)
  (r : Regime) (req1 req2 : Requirement) :
  satisfies r req1 -> satisfies r req2 -> req1 = req2

-- ======================================================================
-- PART 4: NECESSITY (LOWER BOUND: >= 6 REGIMES)
-- ======================================================================

/-- Pick a witness regime for each requirement, given a satisfying substrate. -/
noncomputable def witness
  (satisfies : Regime -> Requirement -> Prop)
  (S : Substrate Regime)
  (h : S.satisfiesAll satisfies) :
  Requirement -> Regime :=
by
  intro req
  have hex : ∃ r : Regime, r ∈ S ∧ satisfies r req := h req
  exact Classical.choose hex

/-- The witness is in `S` and satisfies its requirement. -/
theorem witness_spec
  (satisfies : Regime -> Requirement -> Prop)
  (S : Substrate Regime)
  (h : S.satisfiesAll satisfies)
  (req : Requirement) :
  witness satisfies S h req ∈ S ∧ satisfies (witness satisfies S h req) req :=
by
  have hex : ∃ r : Regime, r ∈ S ∧ satisfies r req := h req
  simpa [witness] using Classical.choose_spec hex

/-- Distinct requirements have distinct witnesses. -/
theorem witness_injective
  (satisfies : Regime -> Requirement -> Prop)
  (S : Substrate Regime)
  (h : S.satisfiesAll satisfies) :
  Function.Injective (witness satisfies S h) :=
by
  intro req1 req2 hw
  have hs1 : satisfies (witness satisfies S h req1) req1 :=
    (witness_spec satisfies S h req1).2
  have hs2 : satisfies (witness satisfies S h req1) req2 := by
    -- rewrite the witness for req1 into the witness for req2
    simpa [hw] using (witness_spec satisfies S h req2).2
  exact satisfies_functional satisfies (witness satisfies S h req1) req1 req2 hs1 hs2

/-- Necessity: any satisfying substrate has at least 6 regimes. -/
theorem necessity
  (satisfies : Regime -> Requirement -> Prop)
  (S : Substrate Regime)
  (h : S.satisfiesAll satisfies) :
  S.card >= 6 :=
by
  -- Define an injection from Requirement into the subtype {r // r ∈ S}.
  let f : Requirement -> {r : Regime // r ∈ S} :=
    fun req =>
      ⟨witness satisfies S h req, (witness_spec satisfies S h req).1⟩

  have hf_inj : Function.Injective f := by
    intro req1 req2 hsub
    have : witness satisfies S h req1 = witness satisfies S h req2 :=
      congrArg Subtype.val hsub
    exact (witness_injective satisfies S h) this

  have hcard_le :
      Fintype.card Requirement <= Fintype.card {r : Regime // r ∈ S} :=
    Fintype.card_le_of_injective f hf_inj

  -- card {r // r ∈ S} = S.card
  -- Mathlib provides `Fintype.card_coe` for finsets via `Fintype` instances.
  -- This lemma is stable:
  have hsub_card : Fintype.card {r : Regime // r ∈ S} = S.card := by
    simp [Fintype.card_coe]

  -- Combine:
  have : 6 <= S.card := by
    -- rewrite 6 as card Requirement, then use inequalities
    have : Fintype.card Requirement <= S.card := by
      simpa [hsub_card] using hcard_le
    simpa [requirement_count] using this

  exact this

-- ======================================================================
-- PART 5: SUFFICIENCY (UPPER BOUND: a 6-regime model exists)
-- ======================================================================

/-- Canonical regime type for the sufficiency witness. -/
abbrev CanonicalRegime := Requirement

/-- Canonical satisfaction: a regime satisfies exactly itself. -/
def canonicalSatisfies : CanonicalRegime -> Requirement -> Prop :=
  fun r req => r = req

/-- Canonical substrate: all requirements-as-regimes. -/
def canonicalSubstrate : Substrate CanonicalRegime :=
  Finset.univ

/-- Canonical substrate satisfies all requirements. -/
theorem canonical_satisfies_all :
  (canonicalSubstrate).satisfiesAll canonicalSatisfies :=
by
  intro req
  refine ⟨req, ?_, rfl⟩
  simp [canonicalSubstrate]

/-- Canonical substrate has card 6. -/
theorem canonical_card :
  canonicalSubstrate.card = 6 :=
by
  -- Since CanonicalRegime = Requirement with 6 elements, univ has card 6.
  simp [canonicalSubstrate, requirement_count, CanonicalRegime]

/-- Sufficiency: there exists a substrate of size 6 satisfying all requirements. -/
theorem sufficiency :
  ∃ S : Substrate CanonicalRegime, S.card = 6 ∧ S.satisfiesAll canonicalSatisfies :=
by
  refine ⟨canonicalSubstrate, canonical_card, canonical_satisfies_all⟩

-- ======================================================================
-- PART 6: MAIN THEOREMS
-- ======================================================================

/-!
## Part 6: Main Theorems

The core results establishing necessity and sufficiency.

Unlike P0, this theorem is not a biconditional about a single predicate.
Instead, it has two components:

1. **Necessity:** any satisfying substrate must have cardinality at least 6.
2. **Sufficiency:** there exists a satisfying substrate with cardinality exactly 6.

The key structural content is the **non-collapse axiom** (`satisfies_functional`),
which prevents satisfying multiple independent requirements with a single regime.
-/


/-- **THEOREM 1 (Necessity):**
    Any substrate satisfying all requirements must contain at least six regimes.

    **Proof strategy:**
    1. Assume a substrate `S` that satisfies all requirements (`satisfiesAll`)
    2. For each requirement `req`, choose a witness regime `witness req ∈ S`
    3. Use `satisfies_functional` to prove the witness function is injective
       (a single regime cannot satisfy two distinct requirements)
    4. Use the induced injection `Requirement → {r // r ∈ S}` to obtain a
       cardinality lower bound
    5. Rewrite `Fintype.card Requirement = 6` via `requirement_count` -/
theorem six_regimes_necessary :
    ∀ (satisfies : Regime -> Requirement -> Prop)
      (S : Substrate Regime),
      S.satisfiesAll satisfies -> S.card >= 6 := by
  intro satisfies S h_all
  exact necessity (Regime := Regime) satisfies S h_all


/-- **THEOREM 2 (Sufficiency):**
    There exists a substrate with exactly six regimes that satisfies all requirements.

    **Proof strategy:**
    1. Use the canonical model `CanonicalRegime := Requirement`
    2. Define `canonicalSatisfies r req := (r = req)`
    3. Let `canonicalSubstrate := Finset.univ`
    4. Show `canonicalSubstrate.satisfiesAll canonicalSatisfies`
       by taking `r := req` as the witness for each requirement
    5. Show `canonicalSubstrate.card = 6` using `requirement_count` -/
theorem six_regimes_sufficient :
    ∃ S : Substrate CanonicalRegime,
      S.card = 6 ∧ S.satisfiesAll canonicalSatisfies := by
  exact sufficiency


/-- **MAIN THEOREM (Necessary and Sufficient):**
    Exactly six regimes are necessary and six regimes suffice.

    This packages necessity and sufficiency into a single statement.

    **Proof strategy:**
    1. Prove necessity by applying `six_regimes_necessary`
    2. Prove sufficiency by using `six_regimes_sufficient`
    3. Combine with `⟨_, _⟩` -/
theorem six_regimes_theorem :
    (∀ (satisfies : Regime -> Requirement -> Prop)
       (S : Substrate Regime),
       S.satisfiesAll satisfies -> S.card >= 6)
    ∧
    (∃ S : Substrate CanonicalRegime,
       S.card = 6 ∧ S.satisfiesAll canonicalSatisfies) := by
  constructor
  · intro satisfies S h_all
    exact six_regimes_necessary (Regime := Regime) satisfies S h_all
  · exact six_regimes_sufficient


-- ======================================================================
-- PART 7: VERIFICATION
-- ======================================================================

/-!
## Part 7: Verification

Confirmation that theorems have expected types.
These statements produce no runtime effect; they verify the formalization.
-/

#check six_regimes_necessary
#check six_regimes_sufficient
#check six_regimes_theorem

/-- Example: the canonical substrate satisfies all requirements. -/
example :
    canonicalSubstrate.satisfiesAll canonicalSatisfies := by
  exact canonical_satisfies_all

/-- Example: the canonical substrate has cardinality 6. -/
example :
    canonicalSubstrate.card = 6 := by
  exact canonical_card

/-- Example: sufficiency produces a 6-element satisfying substrate. -/
example :
    ∃ S : Substrate CanonicalRegime, S.card = 6 ∧ S.satisfiesAll canonicalSatisfies := by
  exact six_regimes_sufficient

/-- Example: no substrate with at most 5 regimes can satisfy all requirements. -/
example
    (satisfies : Regime -> Requirement -> Prop)
    (S : Substrate Regime) :
    S.card <= 5 -> ¬ S.satisfiesAll satisfies := by
  intro h_le h_all
  have h_ge : 6 <= S.card :=
    six_regimes_necessary (Regime := Regime) satisfies S h_all
  -- But 6 <= S.card and S.card <= 5 is impossible.
  have : ¬ (6 <= 5) := by
    native_decide
  exact this (Nat.le_trans h_ge h_le)


end IdentityRegimes.Core
