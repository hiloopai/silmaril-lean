import Silmaril.Prelude.Bytes.Elab.Defs
import Silmaril.Prelude.Bytes.Native.Defs

/-! Kernel-bytes benchmarks (benchmarks/kernel-bytes/README.md). Every timing is wall-clock
around one step, with asynchronous elaboration off so kernel checks happen inside the timer.
Data is pseudo-random (an LCG), so nothing is committed. -/

open Lean Elab Command Meta Silmaril Silmaril.KBytes

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

initialize store : IO.Ref (Std.HashMap Name ByteArray) ← IO.mkRef {}

def nowMs : IO Float := do return (← IO.monoNanosNow).toFloat / 1e6

def report (what : String) (ms : Float) : CommandElabM Unit :=
  logInfo m!"BENCH\t{what}\t{ms}"

def rnd (n seed : Nat) : ByteArray := Id.run do
  let mut s : UInt64 := seed.toUInt64 * 6364136223846793005 + 1442695040888963407
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    s := s * 6364136223846793005 + 1442695040888963407
    b := b.push (s >>> 56).toUInt8
  return b

def kernelCheck (label : String) (e : Expr) : CommandElabM Unit := do
  let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e (mkConst ``Bool.true)
  let pf := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let nm ← liftCoreM <| mkFreshUserName `kc
  let t0 ← nowMs
  try
    liftCoreM <| addDecl (.thmDecl { name := nm, levelParams := [], type := ty, value := pf })
    report s!"kernel {label}" ((← nowMs) - t0)
  catch ex => logError m!"BENCH kernel {label} FAILED {ex.toMessageData}"

def nativeCheck (label : String) (e : Expr) : CommandElabM Unit := do
  let t0 ← nowMs
  match ← liftTermElabM (Meta.nativeEqTrue `bench e) with
  | .success _ => report s!"native {label}" ((← nowMs) - t0)
  | .notTrue => logError m!"BENCH native {label} returned false"

def elabBool (t : Term) : CommandElabM Expr := liftTermElabM do
  let e ← Term.elabTerm t (some (mkConst ``Bool))
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- `#data x N seed [computable]`: random bytes as `kbytes_def` would write them. -/
elab "#data " id:ident n:num seed:num c:(&" computable")? : command => do
  let b := rnd n.getNat seed.getNat
  store.modify (·.insert id.getId b)
  let t0 ← nowMs
  let lits := Elab.chunksOf b Elab.chunkSize
  let t1 ← nowMs
  report s!"encode chunks (interpreted meta code) {n.getNat}" (t1 - t0)
  liftCoreM <| Elab.defineKBytes id.getId Elab.chunkSize b.size lits c.isSome
  report s!"kbytes_def {if c.isSome then "computable" else "noncomputable"} {n.getNat} (defs, eq_ofChunks, wf)" ((← nowMs) - t1)

/-- The whole file as one leaf (the single-`Nat` representation, read by the same `read`). -/
elab "#dataOneLeaf " id:ident src:ident : command => do
  let some b := (← store.get)[src.getId]? | throwError "no data"
  store.modify (·.insert id.getId b)
  let v := Elab.encodeRange b 0 b.size
  let t0 ← nowMs
  liftCoreM <| Elab.addDefn id.getId (mkConst ``KBytes)
    (mkApp2 (mkConst ``KBytes.leaf) (mkNatLit b.size) (mkNatLit v)) false
  report s!"one-leaf def {b.size}" ((← nowMs) - t0)

/-- The bytes as a flat list of 4 KiB literals (the `BinaryImage` layout), byte reads by a walk. -/
def flatByte (c : Nat) (cs : List Nat) (i : Nat) : Nat := (cs.getD (i / c) 0 >>> (8 * (i % c))) % 256

/-- `k` random reads of width `w`, against the bytes, as one conjunction. -/
elab "#reads " id:ident k:num w:num flat:(&" flat")? : command => do
  let some b := (← store.get)[id.getId]? | throwError "no data"
  let w := w.getNat
  let mut s : UInt64 := 77
  let mut e := mkConst ``Bool.true
  for _ in [0:k.getNat] do
    s := s * 6364136223846793005 + 1442695040888963407
    let off := (s >>> 20).toNat % (b.size - w)
    let v := Elab.encodeRange b off (off + w)
    let rd := if flat.isSome then
        mkApp3 (mkConst ``flatByte) (mkNatLit 4096) (mkConst (id.getId ++ `chunks)) (mkNatLit off)
      else mkApp3 (mkConst ``KBytes.read) (mkConst id.getId) (mkNatLit off) (mkNatLit w)
    e := mkApp2 (mkConst ``and) e (mkApp2 (mkConst ``Nat.beq) rd (mkNatLit v))
  kernelCheck s!"{k.getNat} random reads w={w} {if flat.isSome then "flat chunk list" else id.getId.toString}" e

elab "#kcheck " lbl:str t:term : command => do kernelCheck lbl.getString (← elabBool t)
elab "#ncheck " lbl:str t:term : command => do nativeCheck lbl.getString (← elabBool t)

/-- Kernel `rfl` between two constants. -/
elab "#krfl " a:ident b:ident : command => do
  let kb := mkConst ``KBytes
  let nm ← liftCoreM <| mkFreshUserName `kr
  let t0 ← nowMs
  let type := mkApp3 (mkConst ``Eq [1]) kb (mkConst a.getId) (mkConst b.getId)
  let value := mkApp2 (mkConst ``Eq.refl [1]) kb (mkConst a.getId)
  liftCoreM <| addDecl (.thmDecl { name := nm, levelParams := [], type, value })
  report s!"kernel rfl {a.getId} = {b.getId}" ((← nowMs) - t0)
