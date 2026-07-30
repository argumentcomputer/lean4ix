import Lean4Lean.Environment

/-- Minimal downstream consumer of the `Lean4Lean` library: importing
`Lean4Lean.Environment` forces this executable to link the library's module
objects out of the read-only Nix store artifact, and referencing `addDecl`
keeps the dependency honest even under dead-code elimination. The Nix
`downstream-consumer` check builds this package against
`packages.lake-dependency` and asserts this program runs. -/
def main : IO Unit := do
  let _checker := @Lean4Lean.addDecl
  IO.println "consumer-ok"
