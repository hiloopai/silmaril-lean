import Silmaril.X86.Concurrency.Cir.C11.Corpus.Defs

/-!
# Per C11 corpus test: the flags and candidates of each choice of runs

Writes `tools/litmus-x86/export/c11-slices.json`, which `c11 cir` reads to split the kernel
checks of the large tests into slices (see `C11Test.flagsSlice`). Run from the repository root,
after `lake build Silmaril.X86.Concurrency.Cir.C11.Corpus.Defs`:

    lake env lean tools/litmus-x86/lean/C11Slices.lean

The numbers are compiled-code evaluations, used only to choose the slices and to state them;
every slice is then checked by `decide +kernel`, so a wrong number fails the build.
-/

open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.C11
open Silmaril.X86.MemoryModel.Litmus (units rmwPairs candidates)

/-- One test: `[flags, candidates]` per choice of runs, in `C11Test.combos` order. -/
def sliceRow (c : C11Test) : String :=
  let rows := c.combos.map fun trs =>
    let us := units trs
    let evs := us.map Prod.fst
    let exps := us.map Prod.snd
    s!"[{comboFlags c.prog c.tv.test trs}, {(candidates c.tv.test evs exps (rmwPairs evs)).length}]"
  s!"\{\"name\": \"{c.tv.test.name}\", \"combos\": [{", ".intercalate rows}]}"

#eval IO.FS.writeFile "tools/litmus-x86/export/c11-slices.json" <|
  "{\n\"format\": \"silmaril-litmus-c11-slices/1\",\n" ++
  "\"generated_by\": \"lake env lean tools/litmus-x86/lean/C11Slices.lean (do not edit)\",\n" ++
  "\"tests\": [\n" ++ ",\n".intercalate (Corpus.all.map sliceRow) ++ "\n]\n}\n"
