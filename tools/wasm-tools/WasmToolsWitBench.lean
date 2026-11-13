import Silmaril.Wasm.Tools.Component.Cmd.Defs

/-!
# `wasm-tools-witbench`: stage timings of WIT elaboration (benchmark aid)

`wasm-tools-witbench FILE.wit`: lex/parse, validity check, elaboration, binary validity
checks, encoding, decoding and printing of a one-file WIT package, each timed (ms) on stderr.
Used to find the slow stages behind `component wit`/`embed`/`targets` on large worlds
(docs/projects/wasm-wasi.md, performance).
-/

open Silmaril.Wasm

def timeIt {α : Type} (label : String) (x : Unit → Except String α) : IO α := do
  let t0 ← IO.monoMsNow
  let r := x ()
  match r with
  | .ok a =>
    let t1 ← IO.monoMsNow
    IO.eprintln s!"{label}: {t1 - t0} ms"
    pure a
  | .error e => throw (IO.userError s!"{label}: {e}")

def main (args : List String) : IO UInt32 := do
  let path := args.headD "w.wit"
  let text ← IO.FS.readFile path
  let _ ← timeIt "Tool.parseText" fun _ => Wit.Tool.parseText path text
  let _ ← timeIt "Tool.encodeText" fun _ => Wit.Tool.encodeText (path, text) []
  let d ← timeIt "WitDir.parseFiles" fun _ => Wac.WitDir.parseFiles [(path, text)]
  let U := Wit.Tool.sourceUniverse d []
  let _ ← timeIt "check" fun _ => if Wit.check U then .ok () else .error "invalid"
  let c := Wit.Elab.Ctx.ofUniverse U
  let env ← timeIt "elabEnv" fun _ => Wit.Elab.elabEnv c
  let P ← timeIt "lookup" fun _ => Wit.Elab.lookupPkg U d.main.name
  let out ← timeIt "elabPackage" fun _ => Wit.Elab.elabPackage c env P
  let deps := env.filter (·.1.pkg != Wit.Elab.pkgName d.main.name)
  let _ ← timeIt "validB" fun _ => if Wit.Elab.Package.validB out deps then .ok () else .error "validB"
  let _ ← timeIt "namesUniqueB" fun _ => if Wit.Elab.Package.namesUniqueB out then .ok () else .error "names"
  let _ ← timeIt "ifaces unique" fun _ => if out.interfaces.all (fun nb => Wit.Elab.Interface.namesUniqueB nb.2) then .ok () else .error "x"
  let _ ← timeIt "worlds unique" fun _ => if out.worlds.all (fun nw => Wit.Elab.World.namesUniqueB nw.2) then .ok () else .error "x"
  let names := out.worlds.flatMap fun nw => nw.2.exports.map Wit.Binary.WorldItem.key
  let _ ← timeIt "keys" fun _ => .ok names.length
  let _ ← timeIt "nodup keys" fun _ => if decide names.Nodup then .ok () else .error "x"
  let b ← timeIt "encodePackage" fun _ => Wit.Binary.encodePackage deps out
  let dd ← timeIt "decode" fun _ => Wit.Tool.decode b
  let t ← timeIt "witAll" fun _ => Wit.Tool.witAll b
  let _ ← timeIt "fixBytes" fun _ => .ok (Wac.AsyncNames.fixBytes b).size
  let src : Tools.Component.Cmd.WitSrc := .file path text
  let pb ← timeIt "Cmd.pkgBytesF docSrc" fun _ => Tools.Component.Cmd.pkgBytesF [] (Tools.Component.Cmd.docSrc src)
  let _ ← timeIt "Cmd.witOfBinary" fun _ => Tools.Component.Cmd.witOfBinary pb
  let _ ← timeIt "Cmd.witWasmOfSrc" fun _ => Tools.Component.Cmd.witWasmOfSrc (.binary pb)
  IO.eprintln s!"bytes {b.size}, text {t.length}, ifaces {dd.pkg.interfaces.length}"
  pure 0
