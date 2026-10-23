import Lean.Elab.ParseImportsFast
import Cache.Lean

open Lean System

structure ImportAudit where
  visited : Std.HashSet Name := {}
  modules : Array Json := #[]
  missing : Array String := #[]

partial def visitImports (sp : Lean.SearchPath) (mod : Name) (audit : ImportAudit) : IO ImportAudit := do
  if audit.visited.contains mod then return audit
  let audit := { audit with visited := audit.visited.insert mod }
  if [`Init, `Lean, `Std, `Lake].contains mod.getRoot then return audit
  let source <- findLean sp mod
  let some directory <- sp.findWithExtBase "lean" mod
    | throw <| IO.userError s!"No package source directory for {mod}"
  let modulePath := mkFilePath (mod.components.map toString)
  let compiled := directory / ".lake/build/lib/lean" / modulePath.withExtension "olean"
  let present <- compiled.pathExists
  let owned := mod.getRoot == `Cslib
  let record := Json.mkObj [
    ("module", toJson mod.toString), ("source", toJson source.toString),
    ("compiled", toJson compiled.toString), ("compiled_exists", toJson present),
    ("is_cslib", toJson owned)]
  let mut audit := { audit with
    modules := audit.modules.push record
    missing := if owned || present then audit.missing else audit.missing.push mod.toString }
  let parsed <- parseImports' (<- IO.FS.readFile source) source.toString
  for imp in parsed.imports do
    audit <- visitImports sp imp.module audit
  return audit

def main : IO Unit := do
  let audit <- visitImports (<- getSrcSearchPath) `Cslib {}
  IO.println <| (Json.mkObj [
    ("root", toJson "Cslib"), ("modules", toJson audit.modules),
    ("missing_dependency_oleans", toJson audit.missing)]).compress
