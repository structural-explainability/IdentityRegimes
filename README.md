# Structural Explainability: Identity Regimes

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
![Build Status](https://github.com/structural-explainability/IdentityRegimes/actions/workflows/ci.yml/badge.svg?branch=main)
[![Check Links](https://github.com/structural-explainability/IdentityRegimes/actions/workflows/links.yml/badge.svg?branch=main)](https://github.com/structural-explainability/IdentityRegimes/actions/workflows/links.yml)

> Lean 4 formalization of the necessary and sufficient identity-and-persistence regimes for neutral accountability substrates.

## Context

Part of the Structural Explainability framework.

## Scope

The formalization applies to ontological substrates optimized for:

- Stability under durable interpretive disagreement
- Accountability across legal, political, and analytic frameworks
- Neutrality, understood as exclusion of causal and normative execution
- Structural sufficiency

It does not apply to:

- Ontologies embedding causal or normative conclusions
- Systems relying on negotiated or consensus semantics
- Role-based or context-discriminated substrates
- Single-framework modeling environments

## Build and Run

```bash
lake update
lake build
lake exe verify
```

## Documentation

- [Paper to Lean Mapping](./docs/MAPPING.md)
- [Lean 4 Quick Reference](./docs/LEAN.md)

## Citation

See [CITATION.cff](./CITATION.cff)

## License

[MIT](./LICENSE)
