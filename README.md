# Structural Explainability: Identity Regimes

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/license/MIT)
![Build Status](https://github.com/structural-explainability/IdentityRegimes/actions/workflows/ci-lean.yml/badge.svg?branch=main)
[![Check Links](https://github.com/structural-explainability/IdentityRegimes/actions/workflows/links.yml/badge.svg?branch=main)](https://github.com/structural-explainability/IdentityRegimes/actions/workflows/links.yml)

> Superseded Lean 4 formalization of identity-and-persistence regime families
> for neutral accountability substrates.

## Status

This repository is superseded by the active `se-theory-*` and formal-contract repositories.

Active development has moved to:

- [`se-theory-identity-regimes`](https://github.com/structural-explainability/se-theory-identity-regimes)
- [`se-formal-contract`](https://github.com/structural-explainability/se-formal-contract)

This repository is retained for provenance, earlier implementation history,
and compatibility with prior references. It may receive maintenance updates for
tooling, build hygiene, metadata, or release alignment, but it is no longer the
active theory source.

## Scope

This repository provides an earlier Lean 4 formalization of identity-and-persistence
regime families for neutral accountability substrates.

The active theory line now treats the six regime families as a necessary lower
bound under neutrality assumptions and refines them into canonical profile kinds
in `se-theory-identity-regimes`.

The formalization applies to substrates intended to support:

- stability under durable interpretive disagreement;
- accountability across legal, political, and analytic frameworks;
- neutrality as exclusion of causal and normative execution;
- profile-relative identity and persistence.

It does not apply to:

- ontologies embedding causal or normative conclusions;
- systems relying on negotiated or consensus semantics;
- role-based or context-discriminated substrates;
- single-framework modeling environments.

## Current Replacement Path

Use the active repositories for current work:

| Need                                     | Use                                                                                                     |
| ---------------------------------------- | ------------------------------------------------------------------------------------------------------- |
| Active identity-regime theory            | [`se-theory-identity-regimes`](https://github.com/structural-explainability/se-theory-identity-regimes) |
| Machine-readable formal contract exports | [`se-formal-contract`](https://github.com/structural-explainability/se-formal-contract)                 |

## Build and Run

```shell
lake update
lake build
lake exe verify
```

## Documentation

- [Paper to Lean Mapping](./docs/MAPPING.md)
- [Lean 4 Quick Reference](./docs/LEAN.md)

## Annotations

[ANNOTATIONS.md](./ANNOTATIONS.md)

## Citation

[CITATION.cff](./CITATION.cff)

## License

[MIT](./LICENSE)
