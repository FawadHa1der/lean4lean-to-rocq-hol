import Cache.Hashing

open Lean System

def main : IO Unit := Cache.IO.CacheM.run do
  let memo <- Cache.Hashing.getHashMemo {}
  let context <- read
  let mut modules : Array Json := #[]
  let mut missing : Array String := #[]
  for (mod, hash) in memo.hashMap.toArray do
    let directory <- Cache.IO.getSrcDir context.srcSearchPath mod
    let path := mkFilePath (mod.components.map toString)
    let compiled := directory / ".lake/build/lib/lean" / path.withExtension "olean"
    let present <- compiled.pathExists
    let record := Json.mkObj [
      ("module", toJson mod.toString), ("source_directory", toJson directory.toString),
      ("compiled", toJson compiled.toString), ("compiled_exists", toJson present),
      ("cache_file", toJson hash.asLTar)]
    modules := modules.push record
    if !present then missing := missing.push mod.toString
  IO.println <| (Json.mkObj [
    ("root", toJson "Mathlib"), ("modules", toJson modules),
    ("missing_oleans", toJson missing)]).compress
