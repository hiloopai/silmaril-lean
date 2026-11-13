import Silmaril.Wasm.Component.Streams.Chunks.Defs

/-!
# `wasm-wac-spec`: the expected outputs of the WAC stream pipelines, from the Lean transformers

```
wasm-wac-spec CASE CHUNK BYTE...
```

prints, in the WAVE syntax `wasmtime run --invoke` prints, the output of the stream pipeline
`CASE` on the input bytes when the test driver writes them in chunks of `CHUNK` bytes. The
output is `T.run` of the pipeline's Lean transformer (`Silmaril.Wasm.Component.Streams`, the
transformers whose correctness `docs/projects/wasm-wasi.md` proves) on that chunking:

| CASE | Lean transformer | on |
| --- | --- | --- |
| `lpipeline` | `(linesT (· = 10) ⟫ filter (· ≠ [])) ⟫ map (map upper)` | chunks |
| `rpipeline` | `rechunk 3 ⟫ map (map upper)` | chunks |
| `lines` | `linesT (· = 10)` | chunks |
| `rechunk4` | `rechunk 4` | chunks |
| `tpipeline` | `map upper ⟫ tee`, both channels | bytes |
| `tee` | `tee`, both channels | bytes |
| `mpipeline` | `(map upper ⟫ filter (· ≠ 32)) ⟫ take 5` | bytes |
| `upipeline` | `map upper ⟫ filter (· ≠ 32)` | bytes |
| `supper` | `map upper` | bytes |

The chunk transformers are invariant under rechunking (`Tr.run_linesT`, `Tr.run_rechunk`):
the chunking only shows that this holds of the components too. Exit status 2 on a usage error.
-/

open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Tr

/-- Upper-case an ASCII byte. -/
def upper (b : Nat) : Nat := if 97 ≤ b ∧ b ≤ 122 then b - 32 else b

/-- WAVE `list<u8>`. -/
def waveBytes (bs : List Nat) : String :=
  "[" ++ ", ".intercalate (bs.map toString) ++ "]"

/-- WAVE `list<list<u8>>`. -/
def waveChunks (cs : List (List Nat)) : String :=
  "[" ++ ", ".intercalate (cs.map waveBytes) ++ "]"

/-- WAVE `tuple<list<u8>, list<u8>>` of the two channels of a tee. -/
def waveTee (ys : List (Bool × Nat)) : String :=
  "(" ++ waveBytes (chan false ys) ++ ", " ++ waveBytes (chan true ys) ++ ")"

def isNl (b : Nat) : Bool := b == 10

/-- The expected output of a case. -/
def expected (case : String) (chunk : Nat) (input : List Nat) : Option String :=
  let cs := chunksOf (max chunk 1) input
  match case with
  | "lpipeline" =>
    some (waveChunks (((linesT isNl).comp (filter fun l => !l.isEmpty)).comp
      (map fun l => l.map upper) |>.run cs))
  | "rpipeline" => some (waveChunks (((rechunk 3).comp (map fun l => l.map upper)).run cs))
  | "lines" => some (waveChunks ((linesT isNl).run cs))
  | "rechunk4" => some (waveChunks ((rechunk 4).run cs))
  | "tpipeline" => some (waveTee (((map upper).comp tee).run input))
  | "tee" => some (waveTee (tee.run input))
  | "mpipeline" => some (waveBytes ((((map upper).comp (filter (· != 32))).comp (take 5)).run input))
  | "upipeline" => some (waveBytes (((map upper).comp (filter (· != 32))).run input))
  | "supper" => some (waveBytes ((map upper).run input))
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | case :: chunk :: bytes =>
    match chunk.toNat?, bytes.mapM String.toNat? with
    | some c, some bs =>
      match expected case c bs with
      | some s => IO.println s; pure 0
      | none => IO.eprintln s!"wasm-wac-spec: unknown case {case}"; pure 2
    | _, _ => IO.eprintln "usage: wasm-wac-spec CASE CHUNK BYTE..."; pure 2
  | _ => IO.eprintln "usage: wasm-wac-spec CASE CHUNK BYTE..."; pure 2
