import Std

open Std

namespace MkAll

private def baseModule : String := "QuantumSystem"
private def baseDir : System.FilePath := baseModule

private def dropLeanExt (fileName : String) : Option String :=
  if fileName.endsWith ".lean" then
    some (fileName.dropEnd 5 |>.toString)
  else
    none

private def mkModuleName (relDirs : List String) (fileStem : String) : String :=
  String.intercalate "." ([baseModule] ++ relDirs ++ [fileStem])

private partial def walk (dir : System.FilePath) (relDirs : List String) : IO (Array String) := do
  let entries ← System.FilePath.readDir dir
  let mut mods : Array String := #[]
  for entry in entries do
    let fullPath := entry.path
    if (← fullPath.isDir) then
      mods := mods ++ (← walk fullPath (relDirs ++ [entry.fileName]))
    else
      match dropLeanExt entry.fileName with
      | some stem =>
          mods := mods.push (mkModuleName relDirs stem)
      | none =>
          continue
  return mods

private def mkHeader : String :=
  "module\n\n"

private def mkImports (mods : Array String) : String :=
  let lines := mods.toList.map (fun m => s!"public import {m}\n")
  String.join lines

def main : IO Unit := do
  if !(← baseDir.pathExists) then
    IO.eprintln s!"mk_all: directory '{baseDir}' not found (run from repository root)."
    return
  let mods ← walk baseDir []
  let mods := mods.qsort (fun a b =>
    let al := a.toLower
    let bl := b.toLower
    al < bl || (al = bl && a < b))
  let out : System.FilePath := s!"{baseModule}.lean"
  let content := mkHeader ++ mkImports mods
  IO.FS.writeFile out content
  IO.println s!"Updated {out} with {mods.size} public imports from {baseDir}/"

end MkAll

def main : IO Unit := MkAll.main
