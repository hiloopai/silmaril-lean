module

public import Silmaril.Proofs.Project.CompilesTo.O0Entry
public import Silmaril.Proofs.Project.CompilesTo.Epilogue

/-!
# Function-granularity segments: from the call to the return

A function compiled with `-O2` keeps no per-line state, so its `FnData` has one point, the
entry, and its one segment runs from the System V call to the return. Both sides run to the
end:

* `FnData.segment_call`: the segment of a one-point `FnData`, from a run of both sides from
  every corresponding entry to the return (the Core to a final state, the machine to `Returned`
  through no other cut point) with corresponding results.
* The Core side of a **straight-line body** `{ int x₁ = y₁ + z₁; …; int xₙ = yₙ + zₙ;
  return v; }` (`FnData.core_straight`): enter the body and create the block's `int` locals
  (`FnData.enter_run`, the Core part of `FnData.segment_entry`), run the initialisations and
  the return up to the return label (`straight_run`, by induction on the statements, from the
  verified Core library's `init_next` and `ret_jumps`), and the label's body `pure(r)` to the
  procedure's return (`label_run`). The value returned is the sum computed along the
  initialisations (`valsAfter`); every shape hypothesis is decidable (`straightIs`,
  `definedAlong`). An overflow (`Overflows`) is excluded by `Source.Safe`.
* The machine side, one instruction at a time: `step_lea32` (`lea m,%r32`); `step_add32` and
  `step_ret` are in `O0Machine` and `Epilogue`. `FnData.notCut_rsp0`: a state strictly inside
  the code with the entry stack pointer is no cut point.
* `paramDefs_key`: the definition of a parameter is its argument.
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo

open Silmaril.Compiler.CompilesTo

open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Core.Verified
open Silmaril.X86 (Reg)
open Silmaril.X86.Ext (Mem Sz)
open StateMem (Inv Defined defsOf update)
open StateExpr (Term values close)
open ExitCall (Budget)

/-! ## The machine side -/

/-- `lea m, %dst32`: the low half of the effective address, zero-extended. -/
theorem step_lea32 {m : MState} {addr : Nat} {code : List Byte}
    (hl : Silmaril.X86.Ext.Loaded m.memory (BitVec.ofNat 64 addr) code) {o l : Nat}
    (hrip : m.core.rip = BitVec.ofNat 64 (addr + o)) (hfit : o + l ≤ code.length)
    {dst : Reg} {src : Mem}
    (hdec : Silmaril.X86.Open.decode ((code.drop o).take l) =
      some (.base (.lea .d dst src), l)) :
    Silmaril.X86.Open.step m =
      some ⟨{ Sz.d.write m.core dst
          ((src.addr m.core (BitVec.ofNat 64 (addr + o + l))).setWidth 32) with
        rip := BitVec.ofNat 64 (addr + o + l) }, m.memory⟩ := by
  refine Silmaril.X86.Open.step_of_listed hl (rip_add hrip) hfit hdec ?_
  simp only [Silmaril.X86.Ext8.exec_base, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    rip_next hrip]
  rfl

/-- A machine state at an offset that is no point, with the entry stack pointer, is no cut
point of the target: not a program point, and not returned (`rsp` is not past the return
address). -/
theorem FnData.notCut_rsp0 (F : FnData) {k0 : List Frame} {x0 m : MState} {o : Nat}
    (hrip : m.core.rip = BitVec.ofNat 64 (F.addr + o)) (ho : ∀ q ∈ F.points, q.off ≠ o)
    (hlt : o < F.code.length) (hpts : ∀ q ∈ F.points, q.off < F.code.length)
    (haddr : F.addr + F.code.length < 2 ^ 64)
    (hrsp : m.core.read .rsp = x0.core.read .rsp) :
    ¬ (F.corr Silmaril.X86.Open.isa k0).tgtCut x0 m := by
  intro h
  simp only [Corr.tgtCut, FnData.corr, Returned] at h
  rcases h with ⟨j, q, hq, hqrip⟩ | ⟨_, hret⟩
  · have hmem : q ∈ F.points := List.mem_of_getElem? hq
    have hq' : m.core.rip = BitVec.ofNat 64 (F.addr + q.off) := hqrip
    have h1 := congrArg BitVec.toNat (hrip.symm.trans hq')
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by have := hpts q hmem; omega)] at h1
    exact ho q hmem (by omega)
  · rw [hrsp] at hret
    have h3 := congrArg BitVec.toNat hret
    have := (x0.core.read .rsp).isLt
    bv_omega

/-! ## The Core side -/

/-- The definition of the parameter with key `q`, the `i`-th one, is the `i`-th argument. -/
theorem paramDefs_key : ∀ {params : List (Sym × Ctype)} {vs : List Int} {i : Nat}
    {q : StateExpr.Key} {n : Int}, (params.map (·.1.key)).Nodup →
    (params.map (·.1.key))[i]? = some q → vs[i]? = some n →
    Silmaril.Project.Shapes.C.CFn.paramDefs params vs q = some (.lit n)
  | [], _, _, _, _, _, hq, _ => by simp at hq
  | _ :: _, [], _, _, _, _, _, hv => by simp at hv
  | p :: ps, v :: vs, 0, q, n, _, hq, hv => by
    simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hq hv
    subst hq hv
    simp [Silmaril.Project.Shapes.C.CFn.paramDefs, List.zip_cons_cons]
  | p :: ps, v :: vs, i + 1, q, n, hnd, hq, hv => by
    simp only [List.map_cons, List.getElem?_cons_succ] at hq hv
    rw [List.map_cons, List.nodup_cons] at hnd
    have hne : p.1.key ≠ q := by
      intro h
      subst h
      exact hnd.1 (List.mem_of_getElem? hq)
    have hb : (p.1.key == q) = false := by simp [hne]
    have ih := paramDefs_key hnd.2 hq hv
    unfold Silmaril.Project.Shapes.C.CFn.paramDefs at ih ⊢
    simp only [List.zip_cons_cons, List.find?_cons, hb]
    exact ih

/-- **Entering a body `sseq(blk, save)`**: from the Core entry, the body pushes its sequence
frame, creates the block's `int` locals `xs` (new objects below the parameters', without
definitions) and enters the statement `e` of the sequence `sseq(pat, e, rest)` that follows
the creates, with the parameters defined by the arguments. -/
theorem FnData.enter_run (F : FnData) {k0 : List Frame} {vs : List Int} {s : State}
    {a0 : List Annot} {pat0 : Pattern Sym} {blk save : EE} {xs : List Sym}
    {a1 : List Annot} {pat1 : Pattern Sym} {e rest1 : EE}
    (hbody : F.body = .mk a0 (.sseq pat0 blk save))
    (hcr : afterCreates xs blk = some (.mk a1 (.sseq pat1 e rest1)))
    (hnodup : (F.params.map (·.1.key) ++ xs.map (·.key)).Nodup)
    (hroom : 4 * xs.length + 8 ≤ 4096)
    (he : F.CoreEntry k0 vs s) :
    ∃ (env env' : Env) (mem' : Mem.Concrete.State) (ls news : List Local),
      SeqReach.Reaches F.file F.labels s
        ⟨.effectExpr e env', .strongBind pat1 rest1 env' ::
          .strongBind pat0 save env :: .procedureReturn F.bodyLabels :: k0, mem'⟩ ∧
      ls.map (·.sym.key) = F.params.map (·.1.key) ∧ news.map (·.sym.key) = xs.map (·.key) ∧
      Inv env' mem' (ls ++ news) (Silmaril.Project.Shapes.C.CFn.paramDefs F.params vs) ∧ Budget mem' ∧
      vs.length = F.params.length := by
  obtain ⟨hstack, env, hctl, hlen, ls, hlskeys, inv, hroomA⟩ := he
  rcases s with ⟨c, st, mem⟩
  simp only at hstack hctl
  subst hstack hctl
  have hroomA' : 4096 < mem.lastAddress := hroomA.room
  obtain ⟨env', mem', news, rcr, hnews, inv', al', last'⟩ := creates_run (file := F.file)
    (labels := F.labels) xs blk _ hcr env
    (.strongBind pat0 save env :: .procedureReturn F.bodyLabels :: k0) mem ls
    (Silmaril.Project.Shapes.C.CFn.paramDefs F.params vs) inv (AllocRoom.alloc hroomA) (by omega)
    (by rw [hlskeys]; exact hnodup)
  refine ⟨env, env', mem', ls, news, ?_, hlskeys, hnews, inv',
    al'.budget (by rw [last']; omega), hlen⟩
  rw [show F.cfn.body = _ from hbody]
  exact (ReturnConst.sequence_reaches F.file F.labels a0 pat0 blk save env _ mem).trans
    (rcr.trans (ReturnConst.sequence_reaches F.file F.labels a1 pat1 e rest1 env' _ mem'))

/-- The return label's body `pure(r)`, with `r` bound to `v`: three steps (enter the pure
expression, read `r`, leave the diagnostic frame) to the value. -/
theorem label_run {file : Program} {labels : Labels} (r : Sym) {env : Env} {v : Val}
    (h : env.lookup r = some v) (k : List Frame) (m : Mem.Concrete.State) :
    Relation.TransGen (fun s t => ∃ a, Step file labels s a t)
      ⟨.effectExpr (.mk [] (.pure (.mk [] () (.sym r)))) env, k, m⟩ ⟨.value v, k, m⟩ :=
  .head (coreStep (by intro o h; cases h) (request_effect_pure _ _ _ _))
    (.head (coreStep (by intro o h; cases h) (request_pure_sym r env v h _ _))
      (.single (coreStep (by intro o h; cases h) (request_value_diag _ _ m))))

/-! ### A straight-line block -/

/-- `e` is `int x₁ = y₁ + z₁;`, …, `int xₙ = yₙ + zₙ;` (the triples `(xᵢ, yᵢ, zᵢ)` of
`inits`, the `yᵢ`, `zᵢ` keys of locals), then `return v;` (the key `kv`) of the block with the
locals `xs`, along the sequencing continuations: `pat`/`rest` is the continuation of `e`, and
each initialisation is the left side of a sequence `sseq(_, e', rest')` whose right side starts
with the next statement. Decided by the kernel. -/
def straightIs (file : Program) (ret : Sym) (xs : List Sym) (kv : StateExpr.Key) :
    List (Sym × StateExpr.Key × StateExpr.Key) → EE → Pattern Sym → EE → Bool
  | [], e, _, _ => retVarIs file ret xs e kv
  | (x, y, z) :: inits, e, pat, rest =>
    match pat, rest with
    | .mk _ (.base (none, _)), .mk _ (.sseq p' e' rest') =>
      initAddIs file e x y z && straightIs file ret xs kv inits e' p' rest'
    | _, _ => false

theorem straightIs_cons {file : Program} {ret : Sym} {xs : List Sym} {kv : StateExpr.Key}
    {x : Sym} {y z : StateExpr.Key} {inits : List (Sym × StateExpr.Key × StateExpr.Key)}
    {e : EE} {pat : Pattern Sym} {rest : EE}
    (h : straightIs file ret xs kv ((x, y, z) :: inits) e pat rest = true) :
    ∃ pann ty ann p' e' rest', pat = .mk pann (.base (none, ty)) ∧
      rest = .mk ann (.sseq p' e' rest') ∧ initAddIs file e x y z = true ∧
      straightIs file ret xs kv inits e' p' rest' = true := by
  simp only [straightIs] at h
  split at h
  · rename_i pann ty ann p' e' rest'
    simp only [Bool.and_eq_true] at h
    exact ⟨pann, ty, ann, p', e', rest', rfl, rfl, h.1, h.2⟩
  · cases h

/-- The values of the locals after `int x = y + z;` for each `(x, y, z)` of `inits`, from `σ`. -/
def valsAfter : List (Sym × StateExpr.Key × StateExpr.Key) → (StateExpr.Key → Int) →
    StateExpr.Key → Int
  | [], σ => σ
  | (x, y, z) :: inits, σ => valsAfter inits (fun q => if q = x.key then σ y + σ z else σ q)

/-- Each initialisation of `inits` reads keys defined before it (the keys `ks`, then the locals
initialised so far), and the returned key `kv` is defined at the end. Decided by the kernel. -/
def definedAlong : List (Sym × StateExpr.Key × StateExpr.Key) → List StateExpr.Key →
    StateExpr.Key → Bool
  | [], ks, kv => decide (kv ∈ ks)
  | (x, y, z) :: inits, ks, kv =>
      decide (y ∈ ks) && decide (z ∈ ks) && definedAlong inits (x.key :: ks) kv

/-- The values after a definition. -/
theorem values_update (ds : Defs) (q : StateExpr.Key) (d : IntExpr.Term) :
    values (defsOf (update ds q (some d))) =
      fun q' => if q' = q then d.val 0 else values (defsOf ds) q' := by
  funext q'
  unfold values defsOf update
  split <;> rfl

/-- **A straight-line block, up to the return label.** From the statement `e` of a block
`int x₁ = y₁ + z₁; …; return v;` (`straightIs`), each initialisation stores its sum and the
return jumps to the procedure's return label `ret(r)` with `r` bound to the value of `v` after
the initialisations (`valsAfter`), or some operator overflows. -/
theorem straight_run {file : Program} {labels : Labels} {L : Labels} {caller : List Frame}
    {ret r : Sym} {lb : EE} (hlook : L.lookup ret = some ([r], lb)) {xs : List Sym}
    {kv : StateExpr.Key} {lk : List Local} (hnodup : (xs.map (·.key)).Nodup) :
    ∀ (inits : List (Sym × StateExpr.Key × StateExpr.Key)) (e : EE) (pat : Pattern Sym)
      (rest : EE) (env : Env) (m : Mem.Concrete.State) (ls : List Local) (ds : Defs)
      (ks : List StateExpr.Key) (J : List Frame),
    straightIs file ret xs kv inits e pat rest = true → definedAlong inits ks kv = true →
    (∀ q ∈ ks, (ds q).isSome = true) → (∀ i ∈ inits, i.1.key ∈ ls.map (·.sym.key)) →
    StateStmt.Keys lk xs → (∀ l ∈ lk, l ∈ ls) → Inv env m ls ds → Budget m →
    (∀ f ∈ J, ¬ FnData.Boundary f) →
    StateStmt.Overflows (file := file) (labels := labels)
        ⟨.effectExpr e env, .strongBind pat rest env :: (J ++ .procedureReturn L :: caller), m⟩ ∨
      ConvInt.IsInt (valsAfter inits (values (defsOf ds)) kv) ∧ ∃ env' m',
        SeqReach.Reaches file labels
          ⟨.effectExpr e env, .strongBind pat rest env :: (J ++ .procedureReturn L :: caller), m⟩
          ⟨.effectExpr lb
              (extendEnv [(r, IntExpr.spec (valsAfter inits (values (defsOf ds)) kv))] env'),
            .procedureReturn L :: caller, m'⟩
  | [], e, pat, rest, env, m, ls, ds, ks, J, hs, hdef, hks, _, hlk, hsub, inv, _, hJ => by
    have hs' : retVarIs file ret xs e kv = true := hs
    have hkv : (ds kv).isSome = true := by
      simp only [definedAlong, decide_eq_true_eq] at hdef
      exact hks kv hdef
    have hd : Defined ds (.var kv) = true := by simp [Defined, StateExpr.Term.vars, hkv]
    have hctx : StateProc.Context (labels := labels) L caller
        (.strongBind pat rest env :: (J ++ .procedureReturn L :: caller)) := by
      refine context_of (.strongBind pat rest env :: J) fun f hf => ?_
      rcases List.mem_cons.mp hf with rfl | hf
      · simp [FnData.Boundary]
      · exact hJ f hf
    exact ret_jumps hlook (retVarIs_sound hs') inv hlk hsub hnodup hd hctx
  | (x, y, z) :: inits, e, pat, rest, env, m, ls, ds, ks, J, hs, hdef, hks, hloc, hlk, hsub,
      inv, hb, hJ => by
    obtain ⟨pann, ty, ann, p', e', rest', rfl, rfl, hinit, hs'⟩ := straightIs_cons hs
    simp only [definedAlong, Bool.and_eq_true, decide_eq_true_eq] at hdef
    obtain ⟨⟨hy, hz⟩, hdef'⟩ := hdef
    have hd : Defined ds (.bin .add (.var y) (.var z)) = true := by
      simp [Defined, StateExpr.Term.vars, hks y hy, hks z hz]
    obtain ⟨lx, hlx, hlxkey⟩ : ∃ lx ∈ ls, lx.sym.key = x.key :=
      List.mem_map.mp (hloc (x, y, z) (by simp))
    rcases init_next (file := file) (labels := labels) (initAddIs_sound hinit) inv hlx
        hlxkey.symm hd hb pann ty env (J ++ .procedureReturn L :: caller) ann p' e' rest' with
      ub | ⟨-, m', xs', inv', hb', reach⟩
    · exact .inl ub
    let d := close (defsOf ds) (.bin .add (.var y) (.var z))
    have hval : d.val 0 = values (defsOf ds) y + values (defsOf ds) z := by
      show (close (defsOf ds) (.bin .add (.var y) (.var z))).val 0 = _
      rw [StateExpr.close_val]
      rfl
    have hσ : values (defsOf (update ds lx.sym.key (some d))) =
        fun q => if q = x.key then values (defsOf ds) y + values (defsOf ds) z
          else values (defsOf ds) q := by
      rw [values_update, hval, hlxkey]
    have hks' : ∀ q ∈ x.key :: ks, (update ds lx.sym.key (some d) q).isSome = true := by
      intro q hq
      unfold update
      split
      · rfl
      · rename_i hne
        rcases List.mem_cons.mp hq with rfl | hq
        · exact absurd hlxkey.symm hne
        · exact hks q hq
    have hJ' : ∀ f ∈ Frame.annotations xs' :: J, ¬ FnData.Boundary f := by
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · simp [FnData.Boundary]
      · exact hJ f hf
    rcases straight_run hlook hnodup inits e' p' rest' env m' ls _ (x.key :: ks)
        (.annotations xs' :: J) hs' hdef' hks' (fun i hi => hloc i (by simp [hi])) hlk hsub
        inv' hb' hJ' with ub | ⟨hint, env', m'', reach'⟩
    · exact .inl (StateStmt.Overflows.pre reach ub)
    · rw [hσ] at hint reach'
      exact .inr ⟨hint, env', m'', reach.trans reach'⟩

/-- **The Core run of a straight-line body**, from the Core entry to the procedure's return:
the body `sseq(blk, save)` creates the block's `int` locals `xs`, runs
`int x₁ = y₁ + z₁; …; return v;` (`straightIs`, every key read defined: `definedAlong`) and the
return label `ret(r) = pure(r)` (`labelIs`), and ends with the value of `v` computed from the
arguments (`valsAfter`), an `int`. An overflow is excluded by `Safe`. -/
theorem FnData.core_straight (F : FnData) {k0 : List Frame} {vs : List Int} {s : State}
    {a0 : List Annot} {pat0 : Pattern Sym} {blk save : EE} {xs : List Sym}
    {a1 : List Annot} {pat1 : Pattern Sym} {e1 rest1 : EE}
    {inits : List (Sym × StateExpr.Key × StateExpr.Key)} {kv : StateExpr.Key} {r : Sym}
    (hbody : F.body = .mk a0 (.sseq pat0 blk save))
    (hcr : afterCreates xs blk = some (.mk a1 (.sseq pat1 e1 rest1)))
    (hnodup : (F.params.map (·.1.key) ++ xs.map (·.key)).Nodup)
    (hroom : 4 * xs.length + 8 ≤ 4096)
    (hstraight : straightIs F.file (retLabel F.body) xs kv inits e1 pat1 rest1 = true)
    (hdefd : definedAlong inits (F.params.map (·.1.key)) kv = true)
    (hlocals : ∀ i ∈ inits, i.1.key ∈ F.params.map (·.1.key) ++ xs.map (·.key))
    (hlab : labelIs F.bodyLabels (retLabel F.body) r = true)
    (he : F.CoreEntry k0 vs s) (hsafe : (F.source k0).Safe s) :
    ∃ m', Relation.TransGen (F.source k0).step s
        ⟨.value (IntExpr.spec (valsAfter inits (values (defsOf (Silmaril.Project.Shapes.C.CFn.paramDefs F.params vs)))
          kv)), .procedureReturn F.bodyLabels :: k0, m'⟩ ∧
      ConvInt.IsInt (valsAfter inits (values (defsOf (Silmaril.Project.Shapes.C.CFn.paramDefs F.params vs))) kv) := by
  obtain ⟨env, env', mem', ls, news, reach, hls, hnews, inv, hb, hlen⟩ :=
    F.enter_run hbody hcr hnodup hroom he
  have hxs : (xs.map (·.key)).Nodup := (List.nodup_append.mp hnodup).2.1
  have hks : ∀ q ∈ F.params.map (·.1.key), (Silmaril.Project.Shapes.C.CFn.paramDefs F.params vs q).isSome = true :=
    fun q hq => paramDefs_isSome hq hlen
  have hloc : ∀ i ∈ inits, i.1.key ∈ (ls ++ news).map (·.sym.key) := by
    intro i hi
    rw [List.map_append, hls, hnews]
    exact hlocals i hi
  have hJ : ∀ f ∈ [Frame.strongBind pat0 save env], ¬ FnData.Boundary f := by
    intro f hf
    rw [List.mem_singleton] at hf
    subst hf
    simp [FnData.Boundary]
  rcases straight_run (file := F.file) (labels := F.labels) (L := F.bodyLabels) (caller := k0)
      (labelIs_sound hlab) (lk := news) hxs inits e1 pat1 rest1 env' mem' (ls ++ news)
      (Silmaril.Project.Shapes.C.CFn.paramDefs F.params vs) (F.params.map (·.1.key)) [.strongBind pat0 save env]
      hstraight hdefd hks hloc hnews (fun l hl => List.mem_append_right _ hl) inv hb hJ with
    ub | ⟨hint, env'', m'', reach'⟩
  · exact absurd (StateStmt.Overflows.pre reach ub) (Safe.not_overflows hsafe)
  · exact ⟨m'', Relation.TransGen.trans_right (reach.trans reach')
      (label_run r (ConvInt.lookup_one rfl) _ m''), hint⟩

/-! ## The segment of a one-point function -/

/-- **The segment of a one-point function** (`-O2`, function granularity): if point 0 is the
entry and from every System V call with a corresponding, safe Core entry both sides run to the
end (the Core to a final state with a value `v`, the machine to its return through no other cut
point, `Seg`) with corresponding results, the segment at point 0 is simulated. -/
theorem FnData.segment_call (F : FnData) (I : Model) {p0 : Point}
    (hp : F.points[0]? = some p0) (hk : p0.kind = .entry)
    (hrun : ∀ k0 x0 (args : Silmaril.X86.SystemV.CApi.Arguments F.sig.arguments) s,
      MachineEntry F.sig F.addr F.code F.frame args x0 →
      F.CoreEntry k0 (Silmaril.Project.Shapes.C.argValues args) s → (F.source k0).Safe s →
      ∃ t v y, Relation.TransGen (F.source k0).step s t ∧ (F.source k0).final t v ∧
        Seg (F.corr I k0).tgtStep ((F.corr I k0).tgtCut x0) x0 y ∧ Returned x0 y ∧
        F.Result x0 v y) :
    F.Segment I 0 := by
  intro k0 x0 s x _ _ hr hsafe
  obtain ⟨p2, hp2, hholds⟩ := hr
  rw [hp, Option.some.injEq] at hp2
  subst hp2
  rw [hk] at hholds
  obtain ⟨rfl, args, hme, hce⟩ := hholds
  obtain ⟨t, v, y, hst, hfin, hseg, hret, hres⟩ := hrun k0 _ args s hme hce hsafe
  exact ⟨t, y, ⟨hst, Or.inr ⟨v, hfin⟩⟩, hseg, Or.inr ⟨v, hfin, hret, hres⟩⟩

end Silmaril.Project.CompilesTo

end
