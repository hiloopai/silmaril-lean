module

public import Silmaril.Wasm.Component.Streams.Spec.Defs

/-!
# Byte-chunk streams

A stream of bytes travels in **chunks**: each `stream.write`/`stream.read` of the Component Model
copies a batch of items, and the batch boundaries are chosen by the runtime's rendezvous (a read of
`n` items meeting a write of `m` copies `min n m`), not by the program. A transformer of byte
streams should therefore only depend on the **concatenation** of its input chunks. Here a chunk
stream is a `List (List α)` (`α` is `UInt8` for bytes; everything is generic):

* `ChunkEq cs ds`: the two chunk streams have the same concatenation (`cs.flatten = ds.flatten`):
  one is a free reassociation of the other into larger or smaller chunks;
* `Tr.Respects T`: the concatenation of `T`'s whole output depends only on the concatenation of
  its input;
* `Tr.Determined T f`: `T`'s whole output, chunk boundaries included, is `f` of the concatenation
  of its input. A determined transformer respects `ChunkEq` and is moreover **invariant under
  rechunking its input**: the outputs are equal, not only equal up to reassociation.

## Rechunkers

* **Lines.** `cut sep bs` splits `bs` at the separators (the items with `sep x = true`, e.g.
  `(· == 10)` for newline bytes) into the complete lines (separators removed) and the remainder
  after the last separator. `lines sep bs` is the complete lines, then the remainder **if it is
  not empty** (a final line without a trailing newline is emitted at the end of the stream; an
  input ending in a newline has no empty last line). `linesT sep` is the transformer: it keeps the
  current partial line as its state, emits every line as soon as its separator arrives, and emits
  the partial line, if any, when the input ends.
* **Uniform chunks.** `chunksOf n bs` cuts `bs` into chunks of `n` items, the last of `1..n`
  items. `rechunk n` is the transformer: it buffers fewer than `n` items, emits every full chunk as
  soon as it is complete, and emits the nonempty rest at the end.
* `unchunk`: from chunks to items (`flatMap id`); `bytes f`, `bytesFilter p`: a map or filter
  on every item of every chunk.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams

variable {α β : Type}

/-- Two chunk streams with the same concatenation. -/
def ChunkEq (cs ds : List (List α)) : Prop := cs.flatten = ds.flatten

/-! ## Lines -/

/-- Split at the separators (the items with `sep x = true`): the complete lines (without
separators) and the remainder after the last separator. -/
def cut (sep : α → Bool) : List α → List (List α) × List α
  | [] => ([], [])
  | b :: bs =>
    let p := cut sep bs
    if sep b then ([] :: p.1, p.2)
    else
      match p.1 with
      | l :: ls => ((b :: l) :: ls, p.2)
      | [] => ([], b :: p.2)

/-- The lines of `bs`: the complete lines, then the remainder if it is not empty. -/
def lines (sep : α → Bool) (bs : List α) : List (List α) :=
  (cut sep bs).1 ++ (if (cut sep bs).2 = [] then [] else [(cut sep bs).2])

/-! ## Uniform chunks -/

/-- Cut into chunks of `n` items, the last of `1..n` items (`n = 0`: one chunk). -/
def chunksOf (n : Nat) (bs : List α) : List (List α) :=
  if bs = [] then []
  else if n = 0 then [bs]
  else bs.take n :: chunksOf n (bs.drop n)
termination_by bs.length
decreasing_by
  rename_i h hn
  have : bs.length ≠ 0 := by simpa using h
  simp only [List.length_drop]
  omega

namespace Tr

/-- **The line splitter**: the state is the current partial line. -/
def linesT (sep : α → Bool) : Tr (List α) (List α) (List α) where
  init := []
  step buf c := ((cut sep (buf ++ c)).2, (cut sep (buf ++ c)).1)
  flush buf := if buf = [] then [] else [buf]

/-- **The uniform rechunker**: the state is the buffer of fewer than `n` items. -/
def rechunk (n : Nat) : Tr (List α) (List α) (List α) where
  init := []
  step buf c :=
    let b := buf ++ c
    let k := b.length / n * n
    (b.drop k, chunksOf n (b.take k))
  flush buf := if buf = [] then [] else [buf]

/-- From chunks to items. -/
def unchunk : Tr Unit (List α) α := flatMap fun c => c

/-- Map every item of every chunk. -/
def bytes (f : α → β) : Tr Unit (List α) (List β) := map fun c => c.map f

/-- Filter the items of every chunk. -/
def bytesFilter (p : α → Bool) : Tr Unit (List α) (List α) := map fun c => c.filter p

/-- The concatenation of the whole output depends only on the concatenation of the input. -/
def Respects {σ : Type} (T : Tr σ (List α) (List β)) : Prop :=
  ∀ cs ds, ChunkEq cs ds → ChunkEq (T.run cs) (T.run ds)

/-- The whole output is `f` of the concatenation of the input. -/
def Determined {σ γ : Type} (T : Tr σ (List α) γ) (f : List α → List γ) : Prop :=
  ∀ cs, T.run cs = f cs.flatten

end Tr

end Silmaril.Wasm.Component.Streams
