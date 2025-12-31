# Mapping: Narrative Claims to Lean Artifacts

REQ.MAPPING.PURPOSE:
  Provide a stable traceability index from the narrative exposition
  to the Lean formalization.

WHY:
  Locate:
  (a) what is proved, (b) what is assumed (axioms), and
  (c) where each major claim lives in code.


## Public entry point

- `StructuralExplainability/IdentityRegimes.lean` (umbrella import)

## Core result (where to find it)

| Claim (informal) | Lean artifact |
|---|---|
| Lower bound: any satisfying substrate needs at least six regimes | theorem (Necessity) |
| Upper bound: there exists a satisfying substrate with exactly six regimes | theorem (Sufficiency) |
| Bundled statement (if present) | theorem (combined) |

## Explicit assumptions (axioms)

REQ.MAPPING.AXIOMS:
  All non-derived assumptions must be listed here.

| Assumption | Lean artifact | Role |
|---|---|---|
| Independence / non-collapse (one regime cannot discharge two distinct requirements) | axiom | Enables the ≥ 6 lower bound |

## Modules

| Concept | Module |
|---|---|
| Requirements (the finite set of structural roles) | `IdentityRegimes.Core` |
| Substrates / cardinality machinery | `IdentityRegimes.Core` |
| Necessity proof | `IdentityRegimes.Core` |
| Sufficiency construction | `IdentityRegimes.Core` |
