import IdentityRegimes.Conformance
import IdentityRegimes.Core
import IdentityRegimes.Spec

/-!
REQ.PUBLIC.SURFACE:
  Canonical public import surface for this package.
  Do not add any declarations here.
  Do not add empty namespaces.

WHY:
  Downstream projects should have exactly one stable import path for this repo.

OBS:
  - This module re-exports the intended public modules by importing them.
  - It must not define placeholder namespaces.
  - All exported declarations live in imported modules.
-/
