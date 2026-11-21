module

public import Silmaril.Elf.Staged.Reader.Defs
public import Silmaril.Elf.Staged.Decomp.Defs
public import Silmaril.Elf.Region.CFG.Defs
public import Lean.Data.Json

/-! Native discovery and coverage measurement, not proof production. Uses the
same staged ELF readers and canonical decoder as the library certificates.
Build `elf-region-inventory`; run `.lake/build/bin/elf-region-inventory FILE ...`.
Aliases are counted once per (section, address, size); zero-size symbols are
reported separately, never given an inferred extent. IFUNC is excluded.
-/

@[expose] public section

open Lean Silmaril.Elf Silmaril.Elf.Staged Silmaril.Machine.Region.X86.CFG

def measureFile (path : String) : IO Json := do
  let raw ← IO.FS.readBinFile path
  let source := fastRead raw
  let some layout := readLayout.run source | throw <| IO.userError s!"layout rejected: {path}"
  unless layout.header.machine = 62 do throw <| IO.userError s!"not x86-64: {path}"
  let mut entries := 0
  let mut zeroSize := 0
  let mut outside := 0
  let mut extents : Array (Nat × Nat × Nat) := #[]
  let mut decoded := 0
  let mut accepted := 0
  let mut callsReturns := 0
  let mut decodeFailures := 0
  let mut otherFailures := 0
  let mut rows : Array Json := #[]
  for tab in layout.shs do
    if tab.kind = 2 || tab.kind = 11 then
      let some strs := layout.shs[tab.link]? | throw <| IO.userError "missing string table"
      for i in [:tab.size / 24] do
        let some sym := (Parse.symbol strs (tab.offset + 24 * i)).run source
          | throw <| IO.userError "symbol reader rejected"
        if sym.kind = 2 && sym.raw.sectionIndex > 0 && sym.raw.sectionIndex < layout.shs.length then
          entries := entries + 1
          if sym.raw.size = 0 then zeroSize := zeroSize + 1
          else
            let some sh := layout.shs[sym.raw.sectionIndex]? | throw <| IO.userError "missing section"
            let base := sym.raw.value
            let size := sym.raw.size
            if sh.kind != 1 || sh.flags / 4 % 2 != 1 || base < sh.address ||
                sh.address + sh.size < base + size then outside := outside + 1
            else
              let key := (sym.raw.sectionIndex, base, size)
              if !extents.contains key then
                extents := extents.push key
                let off := sh.offset + (base - sh.address)
                if raw.size < off + size then throw <| IO.userError "section exceeds file"
                let bytes := ((raw.extract off (off + size)).toList.map fun x => BitVec.ofNat 8 x.toNat)
                let code : Silmaril.X86.Decompile.Region := ⟨base, bytes⟩
                match code.decode? size with
                | none => decodeFailures := decodeFailures + 1
                | some listing =>
                  decoded := decoded + 1
                  if listing.any (fun d => Silmaril.X86.Decompile.interprocedural d.instr) then
                    callsReturns := callsReturns + 1
                  else
                    let edges := rawEdges listing
                    let row : Row := ⟨code, size, listing, base, edges, outward listing edges⟩
                    if decide row.Valid && (layout.phdrs.find? (codeSeg base size)).isSome then
                      accepted := accepted + 1
                      let name := String.ofList (sym.name.map fun b => Char.ofNat b.toNat)
                      rows := rows.push <| Json.mkObj [
                        ("name", toJson name), ("address", toJson base), ("bytes", toJson size),
                        ("instructions", toJson listing.length), ("outward", toJson row.exits)]
                    else otherFailures := otherFailures + 1
  return Json.mkObj [
    ("file", toJson path), ("definedFunctionSymbolEntries", toJson entries),
    ("zeroSizeEntries", toJson zeroSize), ("outsideExecutableSectionEntries", toJson outside),
    ("distinctNonemptyExecutableExtents", toJson extents.size),
    ("completeCanonicalDecode", toJson decoded), ("decodeRejected", toJson decodeFailures),
    ("decodedCallsOrReturns", toJson callsReturns), ("otherRejected", toJson otherFailures),
    ("acceptedDirectCFG", toJson accepted), ("acceptedCandidates", Json.arr rows)]

def main (args : List String) : IO Unit := do
  let results ← args.mapM measureFile
  (← IO.getStdout).putStrLn (Json.arr results.toArray).pretty
