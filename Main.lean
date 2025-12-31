import IdentityRegimes

-- REQ.EXEC.MAIN:
--   Main entry point for this package.
--
-- WHY:
--   This executable exists solely to ensure that the full
--   formalization compiles end-to-end under CI and local builds.
--
-- OBS:
--   No definitions, theorems, or logic belong here.
--   This file must remain trivial and stable.
--   Any failure here indicates a broken proof or import graph.

def main : IO Unit :=
  IO.println "Success: package verified."
