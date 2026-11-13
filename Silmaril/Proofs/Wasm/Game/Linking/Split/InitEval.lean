module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.GameSub

/-!
# Static linking, separation: initial evaluation

Original module documentation:

# What module initialisation can reach (M3 step B, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3, step (B).

The values that the global initialisers of a module compute (constant expressions, evaluated by
`evalGlobals?` in `instantiateOnce?`) refer only to the module's functions and to the GC objects
allocated by the initialisers themselves; in particular never to an exception or host
reference, nor to an object of the store the module is instantiated in. Ownership of these
objects by the module (`IOwn`) is the starting point of the store split.

* `constInstr?_good`, `constExpr?_good`, `evalConst?_good`, `evalGlobals?_good`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-- What an initialisation that started with `n₀` structs and `m₀` arrays owns at store `s`:
the objects it allocated and the functions `F`. -/
def IOwn (n₀ m₀ : Nat) (F : Nat → Prop) (s : Store H) : Own where
  st a := n₀ ≤ a ∧ a < s.structs.length
  ar a := m₀ ≤ a ∧ a < s.arrays.length
  fn := F
  gl _ := False

theorem Own.GoodRef.mono {O O' : Own} (hst : ∀ a, O.st a → O'.st a) (har : ∀ a, O.ar a → O'.ar a)
    (hfn : ∀ a, O.fn a → O'.fn a) : ∀ {r : Ref}, O.GoodRef r → O'.GoodRef r
  | .i31 _, _ => trivial
  | .null, _ => trivial
  | .struct a, h => hst a h
  | .array a, h => har a h
  | .func a, h => hfn a h
  | .exn _, h => h.elim
  | .host _, h => h.elim
  | .extern r, h => Own.GoodRef.mono hst har hfn (r := r) h

theorem Own.GoodVal.mono {O O' : Own} (hst : ∀ a, O.st a → O'.st a) (har : ∀ a, O.ar a → O'.ar a)
    (hfn : ∀ a, O.fn a → O'.fn a) {v : Val} (h : O.GoodVal v) : O'.GoodVal v := by
  cases v with
  | ref r => exact Own.GoodRef.mono hst har hfn h
  | num => trivial
  | vec => trivial

theorem Own.GoodFV.mono {O O' : Own} (hst : ∀ a, O.st a → O'.st a) (har : ∀ a, O.ar a → O'.ar a)
    (hfn : ∀ a, O.fn a → O'.fn a) {v : FieldVal} (h : O.GoodFV v) : O'.GoodFV v := by
  cases v with
  | val v => exact Own.GoodVal.mono hst har hfn h
  | pack => trivial

theorem IOwn.mono {n₀ m₀ : Nat} {F : Nat → Prop} {s s' : Store H}
    (hs : s.structs.length ≤ s'.structs.length) (ha : s.arrays.length ≤ s'.arrays.length)
    {v : Val} (h : (IOwn n₀ m₀ F s).GoodVal v) : (IOwn n₀ m₀ F s').GoodVal v :=
  Own.GoodVal.mono (O := IOwn n₀ m₀ F s) (O' := IOwn n₀ m₀ F s')
    (fun _ h => ⟨h.1, lt_of_lt_of_le h.2 hs⟩)
    (fun _ h => ⟨h.1, lt_of_lt_of_le h.2 ha⟩) (fun _ h => h) h

theorem IOwn.monoFV {n₀ m₀ : Nat} {F : Nat → Prop} {s s' : Store H}
    (hs : s.structs.length ≤ s'.structs.length) (ha : s.arrays.length ≤ s'.arrays.length)
    {v : FieldVal} (h : (IOwn n₀ m₀ F s).GoodFV v) : (IOwn n₀ m₀ F s').GoodFV v :=
  Own.GoodFV.mono (O := IOwn n₀ m₀ F s) (O' := IOwn n₀ m₀ F s')
    (fun _ h => ⟨h.1, lt_of_lt_of_le h.2 hs⟩)
    (fun _ h => ⟨h.1, lt_of_lt_of_le h.2 ha⟩) (fun _ h => h) h

/-- The objects allocated by the initialisation only refer to what it owns. -/
structure HeapGood (n₀ m₀ : Nat) (F : Nat → Prop) (s : Store H) : Prop where
  st : ∀ a si, n₀ ≤ a → s.structs[a]? = some si → ∀ fv ∈ si.fields, (IOwn n₀ m₀ F s).GoodFV fv
  ar : ∀ a ai, m₀ ≤ a → s.arrays[a]? = some ai → ∀ fv ∈ ai.fields, (IOwn n₀ m₀ F s).GoodFV fv

/-- The globals of the initialisation's frame hold owned values. -/
def GlobalsGood (n₀ m₀ : Nat) (F : Nat → Prop) (f : Frame) (s : Store H) : Prop :=
  ∀ a ∈ f.module.globals, ∀ g, s.globals[a]? = some g → (IOwn n₀ m₀ F s).GoodVal g.value

/-- The facts preserved by one step of constant evaluation. -/
structure CFacts (n₀ m₀ : Nat) (F : Nat → Prop) (s s' : Store H) (vs' : List Val) : Prop where
  vals : ∀ v ∈ vs', (IOwn n₀ m₀ F s').GoodVal v
  heap : HeapGood n₀ m₀ F s'
  structs : s.structs <+: s'.structs
  arrays : s.arrays <+: s'.arrays
  globals : s'.globals = s.globals

theorem HeapGood.addStruct {n₀ m₀ : Nat} {F : Nat → Prop} {s : Store H} (hH : HeapGood n₀ m₀ F s)
    {si : StructInst} (hsi : ∀ fv ∈ si.fields, (IOwn n₀ m₀ F s).GoodFV fv) :
    HeapGood n₀ m₀ F (s.addStruct si) := by
  have hl : s.structs.length ≤ (s.addStruct si).structs.length := by simp [Store.addStruct]
  have hla : s.arrays.length ≤ (s.addStruct si).arrays.length := le_rfl
  refine ⟨fun a si' ha h fv hfv => ?_, fun a ai ha h fv hfv => ?_⟩
  · simp only [Store.addStruct] at h
    rcases getElem?_append_single h with h | ⟨-, rfl⟩
    · exact IOwn.monoFV hl hla (hH.st a si' ha h fv hfv)
    · exact IOwn.monoFV hl hla (hsi fv hfv)
  · exact IOwn.monoFV hl hla (hH.ar a ai ha h fv hfv)

theorem HeapGood.addArray {n₀ m₀ : Nat} {F : Nat → Prop} {s : Store H} (hH : HeapGood n₀ m₀ F s)
    {ai : ArrayInst} (hai : ∀ fv ∈ ai.fields, (IOwn n₀ m₀ F s).GoodFV fv) :
    HeapGood n₀ m₀ F (s.addArray ai) := by
  have hl : s.structs.length ≤ (s.addArray ai).structs.length := le_rfl
  have hla : s.arrays.length ≤ (s.addArray ai).arrays.length := by simp [Store.addArray]
  refine ⟨fun a si ha h fv hfv => ?_, fun a ai' ha h fv hfv => ?_⟩
  · exact IOwn.monoFV hl hla (hH.st a si ha h fv hfv)
  · simp only [Store.addArray] at h
    rcases getElem?_append_single h with h | ⟨-, rfl⟩
    · exact IOwn.monoFV hl hla (hH.ar a ai' ha h fv hfv)
    · exact IOwn.monoFV hl hla (hai fv hfv)

theorem CFacts.same {n₀ m₀ : Nat} {F : Nat → Prop} {s : Store H} {vs' : List Val}
    (hH : HeapGood n₀ m₀ F s) (hv : ∀ v ∈ vs', (IOwn n₀ m₀ F s).GoodVal v) :
    CFacts n₀ m₀ F s s vs' :=
  ⟨hv, hH, List.prefix_refl _, List.prefix_refl _, rfl⟩

theorem popN?_good {vs pre args : List Val} {n : Nat} {P : Val → Prop}
    (h : popN? vs n = some (pre, args)) (hv : ∀ v ∈ vs, P v) :
    (∀ v ∈ pre, P v) ∧ ∀ v ∈ args, P v := by
  obtain ⟨rfl, -⟩ := popN?_eq h
  exact ⟨fun v hv' => hv v (List.mem_append_left _ hv'),
    fun v hv' => hv v (List.mem_append_right _ hv')⟩

theorem structNew?_good {n₀ m₀ : Nat} {F : Nat → Prop} {s s' : Store H} {f : Frame}
    {vs vs' : List Val} {x : TypeIdx} (h : structNew? s f vs x = some (s', vs'))
    (hv : ∀ v ∈ vs, (IOwn n₀ m₀ F s).GoodVal v) (hH : HeapGood n₀ m₀ F s)
    (hn : n₀ ≤ s.structs.length) : CFacts n₀ m₀ F s s' vs' := by
  unfold structNew? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨d, -, fs, -, pre, args, hp, h⟩ := h
  split at h
  case isFalse => cases h
  cases h
  obtain ⟨hpre, hargs⟩ := popN?_good hp hv
  have hl : s.structs.length ≤ (s.addStruct ⟨d, (fs.toList.zip args).map fun (ft, v) =>
      packField (fieldStorage ft) v⟩).structs.length := by simp [Store.addStruct]
  refine ⟨fun v hv' => ?_, hH.addStruct ?_, ?_, List.prefix_refl _, rfl⟩
  · rcases List.mem_append.mp hv' with hv' | hv'
    · exact IOwn.mono (s := s) hl le_rfl (hpre v hv')
    · simp only [List.mem_singleton] at hv'
      subst hv'
      exact ⟨hn, by simp [Store.addStruct]⟩
  · intro fv hfv
    obtain ⟨⟨ft, v⟩, hm, rfl⟩ := List.mem_map.mp hfv
    exact Own.goodFV_packField _ (hargs v (List.of_mem_zip hm).2)
  · simp [Store.addStruct]

theorem arrayNewFixed?_good {n₀ m₀ : Nat} {F : Nat → Prop} {s s' : Store H} {f : Frame}
    {vs vs' : List Val} {x : TypeIdx} {n : Fin (2 ^ 32)}
    (h : arrayNewFixed? s f vs x n = some (s', vs'))
    (hv : ∀ v ∈ vs, (IOwn n₀ m₀ F s).GoodVal v) (hH : HeapGood n₀ m₀ F s)
    (hm : m₀ ≤ s.arrays.length) : CFacts n₀ m₀ F s s' vs' := by
  unfold arrayNewFixed? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨d, -, ft, -, pre, args, hp, h⟩ := h
  split at h
  case isFalse => cases h
  cases h
  obtain ⟨hpre, hargs⟩ := popN?_good hp hv
  have hl : s.arrays.length ≤ (s.addArray ⟨d, args.map (packField (fieldStorage ft))⟩).arrays.length := by
    simp [Store.addArray]
  refine ⟨fun v hv' => ?_, hH.addArray ?_, List.prefix_refl _, ?_, rfl⟩
  · rcases List.mem_append.mp hv' with hv' | hv'
    · exact IOwn.mono (s := s) (by simp [Store.addArray]) hl (hpre v hv')
    · simp only [List.mem_singleton] at hv'
      subst hv'
      exact ⟨hm, by simp [Store.addArray]⟩
  · intro fv hfv
    obtain ⟨v, hv', rfl⟩ := List.mem_map.mp hfv
    exact Own.goodFV_packField _ (hargs v hv')
  · simp [Store.addArray]

theorem global?_good {n₀ m₀ : Nat} {F : Nat → Prop} {s : Store H} {f : Frame} {x : GlobalIdx}
    {a : Nat} {g : GlobalInst} (hG : GlobalsGood n₀ m₀ F f s) (h : s.global? f x = some (a, g)) :
    (IOwn n₀ m₀ F s).GoodVal g.value := by
  rw [global?_eq_some] at h
  exact hG a (List.mem_of_getElem? h.1) g h.2

theorem defaults_good {n₀ m₀ : Nat} {F : Nat → Prop} {s : Store H} {fs : List CFieldType}
    {dvs : List Val} (h : fs.mapM (fun ft => defaultVal? (fieldStorage ft).unpack) = some dvs) :
    ∀ v ∈ dvs, (IOwn n₀ m₀ F s).GoodVal v :=
  (mapM_defaultVal?_ren h Ren.id).2 _

/-- Appending a good value to a list of good values. -/
private theorem goodVals_snoc {P : Val → Prop} {pre : List Val} {w : Val}
    (hp : ∀ v ∈ pre, P v) (hw : P w) : ∀ v ∈ pre ++ [w], P v := by
  intro v hv'
  rcases List.mem_append.mp hv' with hv' | hv'
  · exact hp v hv'
  · have hvw : v = w := List.mem_singleton.mp hv'
    exact hvw ▸ hw

/-- Popping one value off a list of good values. -/
private theorem pop1?_good {P : Val → Prop} {vs pre : List Val} {v : Val}
    (hp : pop1? vs = some (pre, v)) (hv : ∀ w ∈ vs, P w) : (∀ w ∈ pre, P w) ∧ P v := by
  have hvs : vs = pre ++ [v] := pop1?_eq hp
  exact ⟨fun w hw => hv w (hvs ▸ List.mem_append_left _ hw), hv v (by simp [hvs])⟩

/-- Popping two values off a list of good values. -/
private theorem pop2?_good {P : Val → Prop} {vs pre : List Val} {v₁ v₂ : Val}
    (hp : pop2? vs = some (pre, v₁, v₂)) (hv : ∀ w ∈ vs, P w) :
    (∀ w ∈ pre, P w) ∧ P v₁ := by
  have hvs : vs = pre ++ [v₁, v₂] := pop2?_eq hp
  exact ⟨fun w hw => hv w (hvs ▸ List.mem_append_left _ hw), hv v₁ (by simp [hvs])⟩

/-- An instruction that pushes a good value and leaves the store unchanged. -/
private theorem CFacts.push {n₀ m₀ : Nat} {F : Nat → Prop} {s s' : Store H}
    {pre vs' : List Val} {w : Val} (h : some (s, pre ++ [w]) = some (s', vs'))
    (hH : HeapGood n₀ m₀ F s) (hp : ∀ v ∈ pre, (IOwn n₀ m₀ F s).GoodVal v)
    (hw : (IOwn n₀ m₀ F s).GoodVal w) : CFacts n₀ m₀ F s s' vs' := by
  have hs : s = s' ∧ pre ++ [w] = vs' := by simpa only [Option.some.injEq, Prod.mk.injEq] using h
  exact hs.1 ▸ hs.2 ▸ CFacts.same hH (goodVals_snoc hp hw)

private theorem intBinOp_good {n₀ m₀ : Nat} {F : Nat → Prop} {s s' : Store H} {f : Frame}
    {vs vs' : List Val} {t : IntType} {op : IntBinOp}
    (h : constInstr? s f vs (.intBinOp t op) = some (s', vs'))
    (hv : ∀ v ∈ vs, (IOwn n₀ m₀ F s).GoodVal v) (hH : HeapGood n₀ m₀ F s) :
    CFacts n₀ m₀ F s s' vs' := by
  cases hc : constBinOp op
  · simp only [constInstr?, hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  · simp only [constInstr?, hc, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Prod.exists] at h
    obtain ⟨pre, v₁, v₂, hp, x, -, y, -, h⟩ := h
    split at h
    · exact CFacts.push h hH (pop2?_good hp hv).1 trivial
    · cases h

private theorem anyConvertExtern_good {n₀ m₀ : Nat} {F : Nat → Prop} {s s' : Store H}
    {f : Frame} {vs vs' : List Val}
    (h : constInstr? s f vs .anyConvertExtern = some (s', vs'))
    (hv : ∀ v ∈ vs, (IOwn n₀ m₀ F s).GoodVal v) (hH : HeapGood n₀ m₀ F s) :
    CFacts n₀ m₀ F s s' vs' := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨pre, v, hp, h⟩ := h
  have hpv := pop1?_good hp hv
  split at h
  · exact CFacts.push h hH hpv.1 trivial
  · exact CFacts.push h hH hpv.1 hpv.2
  · cases h

private theorem externConvertAny_good {n₀ m₀ : Nat} {F : Nat → Prop} {s s' : Store H}
    {f : Frame} {vs vs' : List Val}
    (h : constInstr? s f vs .externConvertAny = some (s', vs'))
    (hv : ∀ v ∈ vs, (IOwn n₀ m₀ F s).GoodVal v) (hH : HeapGood n₀ m₀ F s) :
    CFacts n₀ m₀ F s s' vs' := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨pre, v, hp, h⟩ := h
  have hpv := pop1?_good hp hv
  split at h
  · split at h
    · exact CFacts.push h hH hpv.1 trivial
    · exact CFacts.push h hH hpv.1 hpv.2
  · cases h

/-- Good values followed by copies of a good value. -/
private theorem goodVals_replicate {P : Val → Prop} {pre : List Val} {v : Val} {k : Nat}
    (hp : ∀ w ∈ pre, P w) (hw : P v) : ∀ w ∈ pre ++ List.replicate k v, P w := by
  intro w hw'
  rcases List.mem_append.mp hw' with hw' | hw'
  · exact hp w hw'
  · exact List.eq_of_mem_replicate hw' ▸ hw

/-- **One constant instruction.** -/
theorem constInstr?_good {n₀ m₀ : Nat} {F : Nat → Prop} {s s' : Store H} {f : Frame}
    {vs vs' : List Val} {i : Instr} (h : constInstr? s f vs i = some (s', vs'))
    (hF : ∀ a ∈ f.module.funcs, F a) (hG : GlobalsGood n₀ m₀ F f s)
    (hv : ∀ v ∈ vs, (IOwn n₀ m₀ F s).GoodVal v) (hH : HeapGood n₀ m₀ F s)
    (hn : n₀ ≤ s.structs.length) (hm : m₀ ≤ s.arrays.length) : CFacts n₀ m₀ F s s' vs' := by
  cases i
  case intConst t x => exact CFacts.push h hH hv trivial
  case floatConst t x => exact CFacts.push h hH hv trivial
  case vecConst b => exact CFacts.push h hH hv trivial
  case refNull ht => exact CFacts.push h hH hv trivial
  case refFunc x =>
    obtain ⟨a, ha, h'⟩ : ∃ a, f.module.funcs[x.toNat]? = some a ∧
        some (s, vs ++ [.ref (.func a)]) = some (s', vs') := by
      simpa only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] using h
    exact CFacts.push h' hH hv (hF a (List.mem_of_getElem? ha))
  case refI31 =>
    obtain ⟨pre, v, hp, iv, -, h'⟩ : ∃ pre v, pop1? vs = some (pre, v) ∧ ∃ iv,
        v.int? .i32 = some iv ∧ some (s, pre ++ [.ref (.i31 (iv.setWidth 31))]) = some (s', vs') := by
      simpa only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] using h
    exact CFacts.push h' hH (pop1?_good hp hv).1 trivial
  case globalGet x =>
    obtain ⟨a, g, hg, h'⟩ : ∃ a g, s.global? f x = some (a, g) ∧
        some (s, vs ++ [g.value]) = some (s', vs') := by
      simpa only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] using h
    exact CFacts.push h' hH hv (global?_good hG hg)
  case intBinOp t op => exact intBinOp_good h hv hH
  case anyConvertExtern => exact anyConvertExtern_good h hv hH
  case externConvertAny => exact externConvertAny_good h hv hH
  case structNew x => exact structNew?_good h hv hH hn
  case structNewDefault x =>
    obtain ⟨d, -, fs, -, dvs, hdvs, h'⟩ : ∃ d, f.type? x = some d ∧ ∃ fs, expandStruct? d = some fs ∧
        ∃ dvs, fs.toList.mapM (fun ft => defaultVal? (fieldStorage ft).unpack) = some dvs ∧
          structNew? s f (vs ++ dvs) x = some (s', vs') := by
      simpa only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] using h
    have hall : ∀ v ∈ vs ++ dvs, (IOwn n₀ m₀ F s).GoodVal v := fun v hv' =>
      (List.mem_append.mp hv').elim (hv v) (defaults_good hdvs v)
    exact structNew?_good h' hall hH hn
  case arrayNew x =>
    show CFacts n₀ m₀ F s s' vs'
    obtain ⟨pre, v, n, hp, k, -, h'⟩ : ∃ pre v n, pop2? vs = some (pre, v, n) ∧ ∃ k,
        n.int? .i32 = some k ∧
          arrayNewFixed? s f (pre ++ List.replicate k.toNat v) x ⟨k.toNat, k.isLt⟩ =
            some (s', vs') := by
      simpa only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] using h
    have hpv : (∀ w ∈ pre, (IOwn n₀ m₀ F s).GoodVal w) ∧ (IOwn n₀ m₀ F s).GoodVal v :=
      pop2?_good hp hv
    exact arrayNewFixed?_good h' (goodVals_replicate hpv.1 hpv.2) hH hm
  case arrayNewDefault x =>
    show CFacts n₀ m₀ F s s' vs'
    obtain ⟨pre, n, hp, k, -, d, -, ft, -, dv, hdv, h'⟩ : ∃ pre n, pop1? vs = some (pre, n) ∧
        ∃ k, n.int? .i32 = some k ∧ ∃ d, f.type? x = some d ∧ ∃ ft, expandArray? d = some ft ∧
          ∃ dv, defaultVal? (fieldStorage ft).unpack = some dv ∧
            arrayNewFixed? s f (pre ++ List.replicate k.toNat dv) x ⟨k.toNat, k.isLt⟩ =
              some (s', vs') := by
      simpa only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] using h
    have hgood : (IOwn n₀ m₀ F s).GoodVal dv := defaultVal?_good hdv
    exact arrayNewFixed?_good h' (goodVals_replicate (pop1?_good hp hv).1 hgood) hH hm
  case arrayNewFixed x n => exact arrayNewFixed?_good h hv hH hm
  all_goals exact absurd h (by simp only [constInstr?, reduceCtorEq, not_false_eq_true])

theorem CFacts.trans {n₀ m₀ : Nat} {F : Nat → Prop} {s s' s'' : Store H} {vs' vs'' : List Val}
    (h₁ : CFacts n₀ m₀ F s s' vs') (h₂ : CFacts n₀ m₀ F s' s'' vs'') : CFacts n₀ m₀ F s s'' vs'' :=
  ⟨h₂.vals, h₂.heap, h₁.structs.trans h₂.structs, h₁.arrays.trans h₂.arrays,
    h₂.globals.trans h₁.globals⟩

/-- The frame's globals exist and hold owned values. -/
def GlobalsOk (n₀ m₀ : Nat) (F : Nat → Prop) (f : Frame) (s : Store H) : Prop :=
  (∀ a ∈ f.module.globals, a < s.globals.length) ∧ GlobalsGood n₀ m₀ F f s

theorem GlobalsOk.mono {n₀ m₀ : Nat} {F : Nat → Prop} {f : Frame} {s s' : Store H}
    (h : GlobalsOk n₀ m₀ F f s) (hg : s'.globals = s.globals)
    (hs : s.structs.length ≤ s'.structs.length) (ha : s.arrays.length ≤ s'.arrays.length) :
    GlobalsOk n₀ m₀ F f s' :=
  ⟨fun a h' => hg ▸ h.1 a h', fun a h' g hg' => IOwn.mono hs ha (h.2 a h' g (hg ▸ hg'))⟩

theorem constFold_good {n₀ m₀ : Nat} {F : Nat → Prop} {f : Frame}
    (hF : ∀ a ∈ f.module.funcs, F a) :
    ∀ (es : List Instr) (st r : Store H × List Val),
      es.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) st = some r →
      GlobalsOk n₀ m₀ F f st.1 → (∀ v ∈ st.2, (IOwn n₀ m₀ F st.1).GoodVal v) →
      HeapGood n₀ m₀ F st.1 → n₀ ≤ st.1.structs.length → m₀ ≤ st.1.arrays.length →
      CFacts n₀ m₀ F st.1 r.1 r.2
  | [], st, r, h, _, hv, hH, _, _ => by
    simp only [List.foldlM, pure, Option.some.injEq] at h
    subst h
    exact .same hH hv
  | i :: es, st, r, h, hG, hv, hH, hn, hm => by
    simp only [List.foldlM, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨st', h1, h2⟩ := h
    have c₁ := constInstr?_good (s' := st'.1) (vs' := st'.2) h1 hF hG.2 hv hH hn hm
    have hs := c₁.structs.length_le
    have ha := c₁.arrays.length_le
    have c₂ := constFold_good hF es st' r h2 (hG.mono c₁.globals hs ha) c₁.vals c₁.heap
      (le_trans hn hs) (le_trans hm ha)
    exact c₁.trans c₂

theorem evalConst?_good {n₀ m₀ : Nat} {F : Nat → Prop} {s s' : Store H} {f : Frame} {e : Expr}
    {v : Val} (h : evalConst? s f e = some (s', v)) (hF : ∀ a ∈ f.module.funcs, F a)
    (hG : GlobalsOk n₀ m₀ F f s) (hH : HeapGood n₀ m₀ F s) (hn : n₀ ≤ s.structs.length)
    (hm : m₀ ≤ s.arrays.length) : CFacts n₀ m₀ F s s' [v] := by
  unfold evalConst? at h
  split at h
  · rename_i s'' w hw
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold constExpr? at hw
    exact constFold_good hF e (s, []) _ hw hG (by simp) hH hn hm
  · cases h

theorem evalGlobals?_good {n₀ m₀ : Nat} {F : Nat → Prop} :
    ∀ {s : Store H} {f : Frame} {gts : List CGlobalType} {es : List Expr} {s₁ : Store H}
      {f₁ : Frame} {vs : List Val},
      evalGlobals? evalConst? s f gts es = some (s₁, f₁, vs) →
      (∀ a ∈ f.module.funcs, F a) → GlobalsOk n₀ m₀ F f s → HeapGood n₀ m₀ F s →
      n₀ ≤ s.structs.length → m₀ ≤ s.arrays.length →
      GlobalsOk n₀ m₀ F f₁ s₁ ∧ HeapGood n₀ m₀ F s₁ ∧ s.structs <+: s₁.structs ∧
        s.arrays <+: s₁.arrays
  | s, f, [], [], s₁, f₁, vs, h, _, hG, hH, _, _ => by
    simp only [evalGlobals?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hG, hH, List.prefix_refl _, List.prefix_refl _⟩
  | s, f, g :: gs, e :: es, s₁, f₁, vs, h, hF, hG, hH, hn, hm => by
    simp only [evalGlobals?] at h
    split at h
    · cases h
    · rename_i s' v he
      split at h
      · cases h
      · rename_i s'' f'' vs' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have c := evalConst?_good he hF hG hH hn hm
        have hs := c.structs.length_le
        have ha := c.arrays.length_le
        have hv : (IOwn n₀ m₀ F s').GoodVal v := c.vals v (by simp)
        have hg := c.globals
        -- the frame after allocating the global
        have hG' : GlobalsOk n₀ m₀ F
            { f with module := { f.module with globals :=
              f.module.globals ++ [(allocGlobal s' g v).2] } } (allocGlobal s' g v).1 := by
          refine ⟨fun a ha' => ?_, fun a ha' gi hgi => ?_⟩
          · simp only [allocGlobal, List.mem_append, List.mem_singleton, List.length_append,
              List.length_singleton] at ha' ⊢
            rcases ha' with ha' | rfl
            · have := hG.1 a ha'; rw [hg]; omega
            · omega
          · simp only [allocGlobal, List.mem_append, List.mem_singleton] at ha' hgi
            rcases getElem?_append_single hgi with hgi | ⟨rfl, rfl⟩
            · rcases ha' with ha' | rfl
              · exact IOwn.mono (s := s) hs ha (hG.2 a ha' gi (hg ▸ hgi))
              · simp at hgi
            · exact hv
        have hH' : HeapGood n₀ m₀ F (allocGlobal s' g v).1 := by
          obtain ⟨h1, h2⟩ := c.heap
          exact ⟨fun a si ha' hsi fv hfv => h1 a si ha' hsi fv hfv,
            fun a ai ha' hai fv hfv => h2 a ai ha' hai fv hfv⟩
        obtain ⟨h1, h2, h3, h4⟩ := evalGlobals?_good hr (by simpa using hF) hG' hH'
          (le_trans hn hs) (le_trans hm ha)
        exact ⟨h1, h2, c.structs.trans h3, c.arrays.trans h4⟩
  | s, f, [], _ :: _, s₁, f₁, vs, h, _, _, _, _, _ => by simp [evalGlobals?] at h
  | s, f, _ :: _, [], s₁, f₁, vs, h, _, _, _, _, _ => by simp [evalGlobals?] at h

/-! ### Single-allocation instantiation -/

/-- What `instantiateOnce?` of a module of the linker's profile produces. -/
structure OnceFacts (s s' : Store H) (m : Module) (as : List Nat) (mi : ModuleInst) : Prop where
  funcs_mi : mi.funcs = as ++ (List.range m.funcs.length).map (s.funcs.length + ·)
  globals_mi : mi.globals = (List.range m.globals.length).map (s.globals.length + ·)
  tags : mi.tags = []
  mems : mi.mems = []
  tables : mi.tables = []
  elems : mi.elems = []
  datas : mi.datas = []
  funcs_prefix : s.funcs <+: s'.funcs
  funcs_new : ∀ k < m.funcs.length, ∃ d fn, s'.funcs[s.funcs.length + k]? = some ⟨d, mi, .wasm fn⟩
  funcs_len : s'.funcs.length = s.funcs.length + m.funcs.length
  globals : s.globals <+: s'.globals
  globals_len : s'.globals.length = s.globals.length + m.globals.length
  structs : s.structs <+: s'.structs
  arrays : s.arrays <+: s'.arrays
  good_globals : ∀ a ∈ mi.globals, ∀ g, s'.globals[a]? = some g →
    (IOwn s.structs.length s.arrays.length (· ∈ mi.funcs) s').GoodVal g.value
  heap : HeapGood s.structs.length s.arrays.length (· ∈ mi.funcs) s'
  exports : ∀ a ∈ Silmaril.Wasm.Game.exportFuncAddrs mi, a ∈ mi.funcs

theorem mapM_some_length {α β : Type _} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ys.length = xs.length :=
  (List.mapM_some_forall₂ (R := fun a b => f a = some b) (fun h => h) h).length_eq.symm

theorem exportFuncAddrs_mem {mi₀ mi : ModuleInst} {es : List Export}
    (h : es.mapM (allocExport? mi₀) = some mi.exports) {a : Nat}
    (ha : a ∈ Silmaril.Wasm.Game.exportFuncAddrs mi) : a ∈ mi₀.funcs := by
  simp only [Silmaril.Wasm.Game.exportFuncAddrs, List.mem_filterMap] at ha
  obtain ⟨x, hx, hxa⟩ := ha
  obtain ⟨e, -, he⟩ := SingleThreaded.mapM_some_mem h x hx
  unfold allocExport? at he
  cases hidx : e.index with
  | func i =>
    rw [hidx] at he
    simp only [Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at he
    obtain ⟨b, hb, hbe⟩ := he
    rw [← hbe] at hxa
    simp only [Option.some.injEq] at hxa
    subst hxa
    exact List.mem_of_getElem? hb
  | _ =>
    rw [hidx] at he
    simp only [Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at he
    obtain ⟨b, -, hbe⟩ := he
    rw [← hbe] at hxa
    simp at hxa

open Silmaril.Wasm.Link.GC in
/-- **Single-allocation instantiation** of a module of the linker's profile, against function
imports. -/
theorem once_facts {s s' : Store H} {m : Module} {as : List Nat} {f' : Frame}
    {st : Option FuncIdx} (hm : inProfile m = true)
    (hp : instantiateOnce? s m (Preparation.imports as) = some (s', f', st)) :
    OnceFacts s s' m as f'.module := by
  obtain ⟨s₁, f₁, values, hg, ha, -, -⟩ := PreparationOnce.once_allocation hm hp
  obtain ⟨hg₁, hf₁, -⟩ := evalGlobals?_shape hg
  have hinit := evalGlobals?_initial hg
  obtain ⟨tagTypes, funcTypes, xi, htt, hft, hexp, hmi, hs'⟩ := allocModule?_inv ha
  have hprof : m.memories = [] ∧ m.tables = [] ∧ m.tags = [] ∧ m.data = [] ∧ m.elems = [] := by
    simp only [inProfile, Bool.and_eq_true, List.isEmpty_iff] at hm
    exact ⟨hm.1.1.1.1.1.1, hm.1.1.1.1.1.2, hm.1.1.1.1.2, hm.1.1.1.2, hm.1.1.2⟩
  obtain ⟨hmem, htab, htag, hdat, hel⟩ := hprof
  simp only [Module.globalResidue, htag, List.mapM_nil, Option.pure_def,
    Option.some.injEq] at htt
  subst tagTypes
  have hftl : funcTypes.length = m.funcs.length := mapM_some_length hft
  have hfuncs : f'.module.funcs = as ++ (List.range m.funcs.length).map (s.funcs.length + ·) := by
    rw [hmi]
    simp [PreparationOnce.residueImports, Module.globalResidue, ExternAddr.funcs_append,
      ExternAddr.funcs_globalAddrs, hf₁]
  have hglobals : f'.module.globals =
      (List.range m.globals.length).map (s.globals.length + ·) :=
    (allocModule?_globalResidue (by simpa [PreparationOnce.residueImports] using ha)).2.trans
      (by simp)
  have hst : s' = { s₁ with funcs := s₁.funcs ++ (funcTypes.zip m.funcs).map fun p =>
      ⟨p.1, f'.module, .wasm p.2⟩ } := by
    rw [hs']
    simp [Module.globalResidue, hmem, htab, hdat, hel]
  -- the initialisers
  have hF : ∀ a ∈ f₁.module.funcs, a ∈ f'.module.funcs := by
    intro a ha'
    rw [hinit] at ha'
    rw [hfuncs]
    simpa [ModuleInst.initial, Module.globalResidue, ExternAddr.funcs_append,
      ExternAddr.funcs_globalAddrs, hf₁] using ha'
  have hG₀ : GlobalsOk s.structs.length s.arrays.length (· ∈ f'.module.funcs)
      ⟨[], ModuleInst.initial s m (Preparation.imports as)⟩ s := by
    refine ⟨fun a ha' => ?_, fun a ha' => ?_⟩ <;> simp [ModuleInst.initial] at ha'
  have hH₀ : HeapGood s.structs.length s.arrays.length (· ∈ f'.module.funcs) s := by
    refine ⟨fun a si ha' h => ?_, fun a ai ha' h => ?_⟩
    · exact absurd (List.getElem?_eq_none ha') (by simp [h])
    · exact absurd (List.getElem?_eq_none ha') (by simp [h])
  have hF₀ : ∀ a ∈ (ModuleInst.initial s m (Preparation.imports as)).funcs,
      a ∈ f'.module.funcs := by
    intro a ha'
    rw [hfuncs]
    simpa [ModuleInst.initial] using ha'
  obtain ⟨hG₁, hH₁, hs₁, ha₁⟩ := evalGlobals?_good hg hF₀ hG₀ hH₀ le_rfl le_rfl
  have hglob₁ : f₁.module.globals = f'.module.globals := by
    rw [hinit, hglobals]
    simp [ModuleInst.initial, Module.globalResidue, ExternAddr.globals_append,
      ExternAddr.globals_globalAddrs, Module.closedGlobalTypes]
  have htags : ∀ l : List Nat, ExternAddr.tags (Preparation.imports l) = [] := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simpa [Preparation.imports, ExternAddr.tags] using ih
  have hmems : ∀ l : List Nat, ExternAddr.mems (Preparation.imports l) = [] := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simpa [Preparation.imports, ExternAddr.mems] using ih
  have htabs : ∀ l : List Nat, ExternAddr.tables (Preparation.imports l) = [] := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simpa [Preparation.imports, ExternAddr.tables] using ih
  have hexports : ∀ a ∈ Silmaril.Wasm.Game.exportFuncAddrs f'.module, a ∈ f'.module.funcs := by
    intro a ha'
    have h1 := exportFuncAddrs_mem (mi := f'.module) (by rw [hmi]; exact hexp) ha'
    rw [hfuncs]
    simpa [PreparationOnce.residueImports, Module.globalResidue, ExternAddr.funcs_append,
      ExternAddr.funcs_globalAddrs, hf₁] using h1
  have hvl := Preparation.evalGlobals_values_length hg
  have hmt : f'.module.tags = [] ∧ f'.module.mems = [] ∧ f'.module.tables = [] ∧
      f'.module.elems = [] ∧ f'.module.datas = [] := by
    rw [hmi]
    simp [PreparationOnce.residueImports, Module.globalResidue, ExternAddr.tags_append,
      ExternAddr.tags_globalAddrs, ExternAddr.mems_append, ExternAddr.mems_globalAddrs,
      ExternAddr.tables_append, ExternAddr.tables_globalAddrs, htags, hmems, htabs, hmem, htab,
      hel, hdat]
  subst hst
  refine ⟨hfuncs, hglobals, hmt.1, hmt.2.1, hmt.2.2.1, hmt.2.2.2.1, hmt.2.2.2.2, ?_, ?_, ?_, ?_,
    ?_, hs₁, ha₁, ?_, ⟨hH₁.st, hH₁.ar⟩, hexports⟩
  · rw [← hf₁]; exact List.prefix_append _ _
  · intro k hk
    have hk' : k < (funcTypes.zip m.funcs).length := by simp [hftl, hk]
    refine ⟨((funcTypes.zip m.funcs)[k]'hk').1, ((funcTypes.zip m.funcs)[k]'hk').2, ?_⟩
    simp only
    rw [← hf₁, List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_eq_getElem hk',
      Option.map_some]
  · simp [hf₁, hftl]
  · rw [hg₁]; exact List.prefix_append _ _
  · simp only [hg₁, List.length_append, List.length_zipWith, Module.closedGlobalTypes,
      List.length_map] at hvl ⊢
    omega
  · intro a ha' g hga
    rw [← hglob₁] at ha'
    exact hG₁.2 a ha' g hga

end Silmaril.Proofs.Wasm.Game.Linking.Split
