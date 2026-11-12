module

public import Silmaril.Wasm.Tools.Dwarf.Frames.Defs

/-!
# addr2line's `find_frames`

`Context.findFrames c probe`: the frames for an address (code-section relative), innermost
first, as addr2line 0.27 yields them: for each inlined call containing the address (deepest
first) a frame with the callee's name, then the function itself; the innermost frame has the
line table's location for the address and every other frame the call site of the frame inside
it. `functions` (`Functions::parse`), `parseFunc` (`Function::parse`) and `inlinedAt`
(`find_inlined_functions`) follow addr2line's code; see `Dwarf.Frames` for units.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Dwarf

/-- A frame: the function's raw name and language, and the location. -/
structure Frame where
  name : Option ByteArray
  lang : Option Nat
  loc : Option Loc

/-- The functions of a unit with addresses: (entry position, its ranges). Sorted ranges with the
index of their function. -/
def functions (c : Context) (u : Unit) : Except String (Array Nat × Array (Range × Nat)) := do
  let go : DR (Array Nat × Array (Range × Nat)) := do
    let mut fs : Array Nat := #[]
    let mut addrs : Array (Range × Nat) := #[]
    let mut w : Walk := {}
    for _ in [0:(← left) + 1] do
      if ← isEmpty then break
      let at_ ← pos
      let (a, w') ← readAbbrevAt u w
      w := w'
      match a with
      | none => pure ()
      | some a =>
        if a.tag == 0x2e then
          let ra ← readAttrs u a ({} : RangeAttrs) fun r n v => r.add c.secs u n v
          let rs ← match ra.ranges c.secs u with
            | .ok x => pure x
            | .error e => throw e
          if !rs.isEmpty then
            let i := fs.size
            fs := fs.push at_
            for r in rs do addrs := addrs.push (r, i)
        else
          let _ ← readAttrs u a () fun _ _ _ => .ok ()
    pure (fs, addrs)
  let ((fs, addrs), _) ← go.run' c.secs.info u.entriesAt u.stop
  pure (fs, (addrs.toList.mergeSort fun a b => a.1.begin ≤ b.1.begin).toArray)

/-- The name of a function or inlined call from its attributes (`linkage_name`, `name`,
`abstract_origin`/`specification`), in attribute order. -/
def nameStep (c : Context) (u : Unit) (nm : Option ByteArray) (n : Nat) (v : AV) :
    Except String (Option ByteArray) :=
  let str := match v with
    | .str x => (x.get (u.strSecs c.secs)).toOption
    | _ => none
  if n == 0x6e || n == 0x2007 then .ok (if str.isSome then str else nm)
  else if n == 0x03 then .ok (if nm.isNone then str else nm)
  else if (n == 0x31 || n == 0x47) && nm.isNone then c.nameAttr 16 u v
  else .ok nm

/-- The state of `Function::parse_children`. -/
structure FState where
  w : Walk := {}
  inlined : Array Inlined := #[]
  addrs : Array (Range × Nat × Nat) := #[]

/-- Skip an entry's attributes and its children (`Function::skip`). -/
def skipTree (u : Unit) (a : Abbrev) (depth : Int) (w : Walk) : DR Walk := do
  let _ ← readAttrs u a () fun _ _ _ => .ok ()
  let mut w := w
  for _ in [0:(← left) + 1] do
    if !(w.depth + w.delta > depth) then break
    let (b, w') ← readAbbrevAt u w
    w := w'
    if let some b := b then let _ ← readAttrs u b () fun _ _ _ => .ok ()
  pure w

/-- `Function::parse_children` (`fuel` bounds the nesting). -/
def parseChildren (c : Context) (u : Unit) : Nat → Int → Nat → FState → DR FState
  | 0, _, _, st => pure st
  | fuel + 1, depth, idepth, st => do
    let mut st := st
    for _ in [0:(← left) + 1] do
      let next := st.w.depth + st.w.delta
      if next ≤ depth then break
      let (a, w') ← readAbbrevAt u st.w
      st := { st with w := w' }
      match a with
      | none => pure ()
      | some a =>
        if a.tag == 0x2e then
          let w ← skipTree u a next st.w
          st := { st with w }
        else if a.tag == 0x1d then
          let (ra, nm, cf, cl, cc) ← readAttrs u a (({} : RangeAttrs), (none : Option ByteArray),
              (none : Option Nat), 0, 0) fun (ra, nm, cf, cl, cc) n v => do
            let ra ← ra.add c.secs u n v
            let nm ← nameStep c u nm n v
            let num := match v with
              | .udata x => some x
              | .sdata x => if x ≥ 0 then some x.toNat else none
              | _ => none
            let cf := if n == 0x58 then
                (match num with
                 | some fi => if fi > 0 || u.version ≥ 5 then some fi else cf
                 | none => cf)
              else cf
            let cl := if n == 0x59 then (num.getD 0) % 2 ^ 32 else cl
            let cc := if n == 0x57 then (num.getD 0) % 2 ^ 32 else cc
            pure (ra, nm, cf, cl, cc)
          let i := st.inlined.size
          st := { st with inlined := st.inlined.push ⟨nm, cf, cl, cc⟩ }
          let rs ← match ra.ranges c.secs u with
            | .ok x => pure x
            | .error e => throw e
          for r in rs do st := { st with addrs := st.addrs.push (r, idepth, i) }
          st ← parseChildren c u fuel next (idepth + 1) st
        else
          let _ ← readAttrs u a () fun _ _ _ => .ok ()
    pure st

/-- **`Function::parse`** at the entry at `at_`. -/
def parseFunc (c : Context) (u : Unit) (at_ : Nat) : Except String Func := do
  let go : DR Func := do
    let w : Walk := {}
    let depth := w.depth + w.delta
    let (a, w) ← readAbbrevAt u w
    let some a := a | throw "No entry at the given offset"
    let nm ← readAttrs u a (none : Option ByteArray) fun nm n v => nameStep c u nm n v
    let st ← parseChildren c u ((← left) + 1) depth 0 { w }
    let addrs := st.addrs.toList.mergeSort fun x y =>
      x.2.1 < y.2.1 || (x.2.1 == y.2.1 && x.1.begin ≤ y.1.begin)
    pure ⟨nm, st.inlined, addrs.toArray⟩
  pure (← go.run' c.secs.info at_ u.stop).1

/-- **`find_inlined_functions`**: the inlined calls containing `probe`, outermost first. -/
def Func.inlinedAt (f : Func) (probe : Nat) : List Inlined := Id.run do
  let mut out : List Inlined := []
  let mut rest := f.addrs
  for _ in [0:f.addrs.size + 1] do
    let d := out.length
    match binarySearch rest (fun (r, dep, _) =>
        if dep > d then .gt else if dep < d then .lt
        else if r.begin > probe then .gt else if r.stop ≤ probe then .lt else .eq) with
    | .ok i =>
      out := out ++ [f.inlined[rest[i]!.2.2]!]
      rest := rest.extract (i + 1) rest.size
    | .error _ => break
  return out

/-- The line table of a unit (none without a line program). -/
def unitLines (c : Context) (u : Unit) : Except String (Option Lines) :=
  match u.lineHeader with
  | none => .ok none
  | some h => some <$> parseLines c.secs.line (u.strSecs c.secs) u.compDir h

/-- The per-unit results addr2line computes once (`LazyFunctions`, `LazyLines`). -/
structure Cache where
  fns : Array (Option (Except String (Array Nat × Array (Range × Nat)))) := #[]
  lines : Array (Option (Except String (Option Lines))) := #[]
  deriving Inhabited

/-- `functions`, through the cache. -/
def Cache.functions (c : Context) (k : Cache) (ui : Nat) : Except String (Array Nat × Array (Range × Nat)) × Cache :=
  match k.fns[ui]?.join with
  | some r => (r, k)
  | none =>
    let r := Dwarf.functions c c.units[ui]!.unit
    let fns := if k.fns.size ≤ ui then k.fns ++ Array.replicate (ui + 1 - k.fns.size) none else k.fns
    (r, { k with fns := fns.set! ui (some r) })

/-- `unitLines`, through the cache. -/
def Cache.unitLines (c : Context) (k : Cache) (ui : Nat) : Except String (Option Lines) × Cache :=
  match k.lines[ui]?.join with
  | some r => (r, k)
  | none =>
    let r := Dwarf.unitLines c c.units[ui]!.unit
    let ls := if k.lines.size ≤ ui then k.lines ++ Array.replicate (ui + 1 - k.lines.size) none else k.lines
    (r, { k with lines := ls.set! ui (some r) })

/-- **`find_frames`**, with the per-unit cache. -/
def Context.findFramesC (c : Context) (k : Cache) (probe : Nat) : Except String (List Frame) × Cache := Id.run do
  let mut k := k
  for ui in c.find probe do
    let ru := c.units[ui]!
    let u := ru.unit
    let (rf, k1) := Cache.functions c k ui
    k := k1
    let (fs, addrs) ← match rf with
      | .ok x => pure x
      | .error e => return (.error e, k)
    let fn ← match binarySearch addrs (fun (r, _) =>
        if probe < r.begin then .gt else if probe ≥ r.stop then .lt else .eq) with
      | .ok i => match parseFunc c u fs[addrs[i]!.2]! with
        | .ok f => pure (some f)
        | .error e => return (.error e, k)
      | .error _ => pure none
    let (rl, k2) := Cache.unitLines c k ui
    k := k2
    let lines ← match rl with
      | .ok x => pure x
      | .error e => return (.error e, k)
    let loc := lines.bind (·.findLocation probe)
    match fn with
    | some f =>
      let inl := f.inlinedAt probe
      let mut frames : List Frame := []
      let mut next := loc
      for g in inl.reverse do
        frames := frames ++ [⟨g.name, ru.lang, next⟩]
        let file := match g.callFile, lines with
          | some fi, some ls => ls.files[fi]?
          | _, _ => none
        next := some ⟨file, if g.callLine != 0 then some g.callLine else none,
          if g.callColumn != 0 then some g.callColumn else none⟩
      return (.ok (frames ++ [⟨f.name, ru.lang, next⟩]), k)
    | none =>
      if loc.isSome then return (.ok [⟨none, none, loc⟩], k)
  return (.ok [], k)

/-- **`find_frames`** (no cache). -/
def Context.findFrames (c : Context) (probe : Nat) : Except String (List Frame) :=
  (c.findFramesC {} probe).1

end Silmaril.Wasm.Tools.Dwarf

end
