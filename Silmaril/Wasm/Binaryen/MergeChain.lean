module

public import Silmaril.Wasm.Binaryen.MergeUntyped
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateIff
public import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc
public import Silmaril.Wasm.Link.OrdinaryInitializers

@[expose] public section

/-! # Chains of linked stores

`StoreRelation.Related` is not transitive (its function relation relocates code
once), so an N-ary merge relates separate instantiation and merged instantiation by
a *chain* of store links (`Chain`): each link is the linking relation (with a valid
source, `Link.related`) or a global-address renaming (`Link.renamed`). Each link
keeps behaviour sets (`MergeUntyped.related_behaviours`, `renamed_behaviours`), so a
chain does too (`Chain.behaviours`).

A chain is extended by instantiating the same module on both ends (`Chain.prepare`):
ordinary preparation in the linker's profile only reads the structures and arrays,
the global and function counts and the globals it allocates itself, so the two
preparations allocate the same globals, structures, arrays and functions
(`prepare_congr`), and every link survives.
-/

namespace Silmaril.Wasm.Binaryen.MergeChain

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Link.GC Silmaril.Wasm.Link.GC.Preparation
open Silmaril.Wasm.Binaryen.MergeUntyped

variable {H : Type}

/-! ## Links and chains -/

/-- One link of a store chain. -/
inductive Link : Store H → Store H → Prop where
  | related {s t : Store H} (h : StoreRelation.Related s t) (ok : StoreOk s) : Link s t
  | renamed {s t : Store H} {p : Nat ≃ Nat} (h : GlobalPermutation.Renamed p s t)
      (fix : ∀ a, s.globals.length ≤ a → p a = a) (len : s.globals.length = t.globals.length) :
      Link s t

/-- A chain of links from separate to merged instantiation. -/
inductive Chain : Store H → Store H → Prop where
  | refl (s : Store H) : Chain s s
  | cons {s t u : Store H} (h : Link s t) (c : Chain t u) : Chain s u

theorem Link.behaviours {o : SingleThreaded.GrowOracle} {s t : Store H} (h : Link s t)
    (a : Nat) (vs : List Val) :
    behaviours (SingleThreaded.profile o) Simulation.noHost t a vs =
      behaviours (SingleThreaded.profile o) Simulation.noHost s a vs := by
  cases h with
  | related h ok => exact related_behaviours h (storeSc_of_ok ok) a vs
  | renamed h _ _ => exact renamed_behaviours h a vs

/-- **A chain keeps behaviour sets**, for every argument list. -/
theorem Chain.behaviours {o : SingleThreaded.GrowOracle} {s u : Store H} (h : Chain s u)
    (a : Nat) (vs : List Val) :
    behaviours (SingleThreaded.profile o) Simulation.noHost u a vs =
      behaviours (SingleThreaded.profile o) Simulation.noHost s a vs := by
  induction h with
  | refl => rfl
  | cons hl _ ih => rw [ih, hl.behaviours]

theorem Chain.append {s t u : Store H} (h : Chain s t) (h' : Chain t u) : Chain s u := by
  induction h with
  | refl => exact h'
  | cons hl _ ih => exact .cons hl (ih h')

theorem Link.funcs_length {s t : Store H} (h : Link s t) : s.funcs.length = t.funcs.length := by
  cases h with
  | related h _ => exact h.functions.length_eq
  | renamed h _ _ => rw [h.functions, List.length_map]

theorem Chain.funcs_length {s t : Store H} (h : Chain s t) : s.funcs.length = t.funcs.length := by
  induction h with
  | refl => rfl
  | cons hl _ ih => exact hl.funcs_length.trans ih

theorem Link.tag_lookup {s t : Store H} (h : Link s t) (a : Nat) :
    s.funcs[a]?.map FuncInst.type = t.funcs[a]?.map FuncInst.type := by
  cases h with
  | related h _ => exact h.function_tag_lookup a
  | renamed h _ _ => exact h.function_tag_lookup a

theorem Chain.tag_lookup {s t : Store H} (h : Chain s t) (a : Nat) :
    s.funcs[a]?.map FuncInst.type = t.funcs[a]?.map FuncInst.type := by
  induction h with
  | refl => rfl
  | cons hl _ ih => exact (hl.tag_lookup a).trans ih

/-- Function import typing depends only on the closed tags of the store. -/
theorem externAddrOk_func {s t : Store H} {a : Nat} {xt : CExternType}
    (htag : s.funcs[a]?.map FuncInst.type = t.funcs[a]?.map FuncInst.type)
    (h : ExternAddrOk s (.func a) xt) : ExternAddrOk t (.func a) xt := by
  generalize hx : ExternAddr.func a = xa at h
  induction h with
  | func hf =>
    cases hx
    rw [hf, Option.map_some] at htag
    obtain ⟨fi', hf', heq⟩ := Option.map_eq_some_iff.mp htag.symm
    rw [← heq]
    exact .func hf'
  | sub _ hok hs ih => exact .sub (ih hx) hok hs
  | _ => cases hx

theorem Chain.externAddrOk {s t : Store H} (h : Chain s t) {a : Nat} {xt : CExternType}
    (hx : ExternAddrOk s (.func a) xt) : ExternAddrOk t (.func a) xt :=
  externAddrOk_func (h.tag_lookup a) hx

/-! ## Constant evaluation reads only structures, arrays and its own globals -/

/-- Equal structures and arrays. -/
structure SA (X Y : Store H) : Prop where
  structs : X.structs = Y.structs
  arrays : X.arrays = Y.arrays

theorem SA.addStruct {X Y : Store H} (h : SA X Y) (v : StructInst) :
    SA (X.addStruct v) (Y.addStruct v) :=
  ⟨by simp [Store.addStruct, h.structs], by simpa [Store.addStruct] using h.arrays⟩

theorem SA.addArray {X Y : Store H} (h : SA X Y) (v : ArrayInst) :
    SA (X.addArray v) (Y.addArray v) :=
  ⟨by simpa [Store.addArray] using h.structs, by simp [Store.addArray, h.arrays]⟩

theorem structNew_congr {X Y X' : Store H} {f : Frame} {vs out : List Val} {x : TypeIdx}
    (h : SA X Y) (run : structNew? X f vs x = some (X', out)) :
    ∃ Y', structNew? Y f vs x = some (Y', out) ∧ SA X' Y' := by
  simp only [structNew?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨d, hd, fs, hf, pre, args, hp, run⟩ := run
  split at run
  · rename_i hall
    cases run
    refine ⟨_, ?_, h.addStruct _⟩
    simp only [structNew?, Option.bind_eq_bind, hd, Option.bind_some, hf, hp,
      ite_eq_left hall, ← h.structs]
  · cases run

theorem arrayNewFixed_congr {X Y X' : Store H} {f : Frame} {vs out : List Val} {x : TypeIdx}
    {n : Fin (2^32)} (h : SA X Y) (run : arrayNewFixed? X f vs x n = some (X', out)) :
    ∃ Y', arrayNewFixed? Y f vs x n = some (Y', out) ∧ SA X' Y' := by
  simp only [arrayNewFixed?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨d, hd, ft, hf, pre, args, hp, run⟩ := run
  split at run
  · rename_i hall
    cases run
    refine ⟨_, ?_, h.addArray _⟩
    simp only [arrayNewFixed?, Option.bind_eq_bind, hd, Option.bind_some, hf, hp,
      ite_eq_left hall, ← h.arrays]
  · cases run

/-- Globals the frame can read hold the same values in both stores. -/
def Agree (X Y : Store H) (f : Frame) : Prop := ∀ a ∈ f.module.globals, X.globals[a]? = Y.globals[a]?

theorem constInstr_congr {X Y X' : Store H} {f : Frame} {vs out : List Val} {i : Instr}
    (h : SA X Y) (hg : Agree X Y f) (run : constInstr? X f vs i = some (X', out)) :
    ∃ Y', constInstr? Y f vs i = some (Y', out) ∧ SA X' Y' := by
  cases i <;> simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    reduceCtorEq, Prod.exists] at run
  case intConst t x => cases run; exact ⟨Y, rfl, h⟩
  case floatConst t x => cases run; exact ⟨Y, rfl, h⟩
  case vecConst b => cases run; exact ⟨Y, rfl, h⟩
  case refNull ht => cases run; exact ⟨Y, rfl, h⟩
  case refFunc x =>
    obtain ⟨a, ha', run⟩ := run
    cases run
    exact ⟨Y, by simp only [constInstr?, Option.bind_eq_bind, ha', Option.bind_some], h⟩
  case refI31 =>
    obtain ⟨pre, v, hp, b, hb, run⟩ := run
    cases run
    exact ⟨Y, by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, hb], h⟩
  case globalGet x =>
    obtain ⟨a, g, hg', run⟩ := run
    cases run
    refine ⟨Y, ?_, h⟩
    simp only [Store.global?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at hg'
    obtain ⟨a', ha', g', hg'', rfl, rfl⟩ := hg'
    have hY : Y.globals[a']? = some g' := by
      rw [← hg a' (List.mem_of_getElem? ha')]
      exact hg''
    simp only [constInstr?, Store.global?, ha', hY, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]
  case intBinOp t op =>
    split at run
    · rename_i hop
      simp only [Option.bind_eq_some_iff, Prod.exists] at run
      obtain ⟨pre, v₁, v₂, hp, x, hx, y, hy, run⟩ := run
      split at run
      · rename_i z hz
        cases run
        exact ⟨Y, by simp only [constInstr?, Option.bind_eq_bind, ite_eq_left hop, hp,
          Option.bind_some, hx, hy, hz], h⟩
      · cases run
    · cases run
  case anyConvertExtern =>
    obtain ⟨pre, v, hp, run⟩ := run
    split at run
    · cases run
      exact ⟨Y, by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some], h⟩
    · cases run
      exact ⟨Y, by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some], h⟩
    · cases run
  case externConvertAny =>
    obtain ⟨pre, v, hp, run⟩ := run
    split at run
    · split at run
      · cases run
        exact ⟨Y, by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some]
                     split <;> simp_all, h⟩
      · cases run
        exact ⟨Y, by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some]
                     split <;> simp_all, h⟩
    · cases run
  case structNew x => exact structNew_congr h run
  case structNewDefault x =>
    obtain ⟨d, hd, fs, hf, dvs, hv, run⟩ := run
    obtain ⟨Y', ht, h'⟩ := structNew_congr h run
    exact ⟨Y', by simp only [constInstr?, Option.bind_eq_bind, hd, Option.bind_some, hf, hv]
                  exact ht, h'⟩
  case arrayNew x =>
    obtain ⟨pre, v, nv, hp, n, hn, run⟩ := run
    obtain ⟨Y', ht, h'⟩ := arrayNewFixed_congr h run
    exact ⟨Y', by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, hn]
                  exact ht, h'⟩
  case arrayNewDefault x =>
    obtain ⟨pre, nv, hp, n, hn, d, hd, ft, hf, v, hv, run⟩ := run
    obtain ⟨Y', ht, h'⟩ := arrayNewFixed_congr h run
    exact ⟨Y', by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, hn, hd,
                    hf, hv]
                  exact ht, h'⟩
  case arrayNewFixed x n => exact arrayNewFixed_congr h run

theorem constExpr_congr {X Y X' : Store H} {f : Frame} {out : List Val} {e : Expr}
    (h : SA X Y) (hg : Agree X Y f) (run : constExpr? X f e = some (X', out)) :
    ∃ Y', constExpr? Y f e = some (Y', out) ∧ SA X' Y' := by
  unfold constExpr? at run ⊢
  suffices ∀ (es : Expr) (X₀ Y₀ X₁ : Store H) (vs out : List Val),
      X₀.globals = X.globals → Y₀.globals = Y.globals → SA X₀ Y₀ →
      es.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) (X₀, vs) =
        some (X₁, out) →
      ∃ Y₁, es.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) (Y₀, vs) =
        some (Y₁, out) ∧ SA X₁ Y₁ from
    this e X Y X' [] out rfl rfl h run
  intro es
  induction es with
  | nil =>
    intro X₀ Y₀ X₁ vs out _ _ h₀ run
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨Y₀, rfl, h₀⟩
  | cons i es ih =>
    intro X₀ Y₀ X₁ vs out hX hY h₀ run
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨X₂, vs₂⟩, h₁, h₂⟩ := run
    have hg₀ : Agree X₀ Y₀ f := fun a ha => by rw [hX, hY]; exact hg a ha
    obtain ⟨Y₂, ht₁, h₂'⟩ := constInstr_congr h₀ hg₀ h₁
    have hX₂ : X₂.globals = X.globals := (constInstr?_shape h₁).1.trans hX
    have hY₂ : Y₂.globals = Y.globals := (constInstr?_shape ht₁).1.trans hY
    obtain ⟨Y₁, ht₂, h₁'⟩ := ih X₂ Y₂ X₁ vs₂ out hX₂ hY₂ h₂' h₂
    exact ⟨Y₁, by simp only [List.foldlM_cons, Option.bind_eq_bind, ht₁, Option.bind_some]
                  exact ht₂, h₁'⟩

theorem evalConst_congr {X Y X' : Store H} {f : Frame} {e : Expr} {v : Val}
    (h : SA X Y) (hg : Agree X Y f) (run : evalConst? X f e = some (X', v)) :
    ∃ Y', evalConst? Y f e = some (Y', v) ∧ SA X' Y' := by
  unfold evalConst? at run
  split at run
  · rename_i X₀ v₀ hc
    cases run
    obtain ⟨Y', ht, h'⟩ := constExpr_congr h hg hc
    exact ⟨Y', by simp only [evalConst?, ht], h'⟩
  · cases run

theorem getElem?_append_congr {α : Type} {l₁ l₂ m : List α} {a : Nat}
    (hl : l₁.length = l₂.length) (h : l₁[a]? = l₂[a]?) : (l₁ ++ m)[a]? = (l₂ ++ m)[a]? := by
  by_cases ha : a < l₁.length
  · rw [List.getElem?_append_left ha, List.getElem?_append_left (by omega), h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hl]

theorem Agree.alloc {X Y : Store H} {f : Frame} (hg : Agree X Y f)
    (hl : X.globals.length = Y.globals.length) (g : CGlobalType) (v : Val) :
    Agree (allocGlobal X g v).1 (allocGlobal Y g v).1
      { f with module := { f.module with globals := f.module.globals ++ [(allocGlobal X g v).2] } } := by
  intro a ha
  simp only [allocGlobal, List.mem_append, List.mem_singleton] at ha ⊢
  rcases ha with ha | rfl
  · exact getElem?_append_congr hl (hg a ha)
  · refine getElem?_append_congr hl ?_
    rw [List.getElem?_eq_none (le_refl _), List.getElem?_eq_none (by omega)]

theorem evalGlobals_congr {types : List CGlobalType} :
    ∀ {es : List Expr} {X Y X₁ : Store H} {f f₁ : Frame} {vals : List Val},
      evalGlobals? evalConst? X f types es = some (X₁, f₁, vals) →
      SA X Y → X.globals.length = Y.globals.length → Agree X Y f →
      ∃ Y₁, evalGlobals? evalConst? Y f types es = some (Y₁, f₁, vals) ∧ SA X₁ Y₁ := by
  induction types with
  | nil =>
    intro es X Y X₁ f f₁ vals run h _ _
    cases es with
    | nil =>
      simp only [evalGlobals?, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      exact ⟨Y, rfl, h⟩
    | cons e es => simp only [evalGlobals?, reduceCtorEq] at run
  | cons type types ih =>
    intro es X Y X₁ f f₁ vals run h hl hg
    cases es with
    | nil => simp only [evalGlobals?, reduceCtorEq] at run
    | cons e es =>
      simp only [evalGlobals?] at run
      split at run
      · cases run
      · rename_i X' v he
        split at run
        · cases run
        · rename_i X'' f'' vs' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl, rfl⟩ := run
          obtain ⟨Y', hY', h'⟩ := evalConst_congr h hg he
          have hX'g := (evalConst?_shape he).1
          have hY'g := (evalConst?_shape hY').1
          have hl' : X'.globals.length = Y'.globals.length := by rw [hX'g, hY'g, hl]
          have hg' : Agree X' Y' f := fun a h => by rw [hX'g, hY'g]; exact hg a h
          have haddr : (allocGlobal Y' type v).2 = (allocGlobal X' type v).2 := by
            simp only [allocGlobal, hl']
          have hga := hg'.alloc hl' type v
          rw [← haddr] at hr hga
          obtain ⟨Y'', hY'', h''⟩ := ih (Y := (allocGlobal Y' type v).1) hr ⟨h'.structs, h'.arrays⟩
            (by simp only [allocGlobal, List.length_append, hl']) hga
          refine ⟨Y'', ?_, h''⟩
          simp only [evalGlobals?, hY', hY'']


/-- The converse of `allocModule?_inv`: its witnesses determine the allocation. -/
theorem allocModule?_of {s : Store H} {m : Module} {xas : List ExternAddr} {valsG : List Val}
    {refsT : List Ref} {refsE : List (List Ref)} {tagTypes funcTypes : List DefType}
    {xi : List ExportInst} {mi : ModuleInst}
    (ht : m.tags.mapM (fun x => (allocTypes m.types)[x.toNat]?) = some tagTypes)
    (hf : m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some funcTypes)
    (hx : m.exports.mapM (allocExport?
        { tags := ExternAddr.tags xas ++ List.range' s.tags.length tagTypes.length,
          globals := ExternAddr.globals xas ++ List.range' s.globals.length
            (min m.globals.length valsG.length),
          mems := ExternAddr.mems xas ++ List.range' s.mems.length m.memories.length,
          tables := ExternAddr.tables xas ++ List.range' s.tables.length
            (min m.tables.length refsT.length),
          funcs := ExternAddr.funcs xas ++
            (List.range m.funcs.length).map (s.funcs.length + ·) }) = some xi)
    (hmi : mi = {
             types := allocTypes m.types,
             tags := ExternAddr.tags xas ++ List.range' s.tags.length tagTypes.length,
             globals := ExternAddr.globals xas ++ List.range' s.globals.length
              (min m.globals.length valsG.length),
             mems := ExternAddr.mems xas ++ List.range' s.mems.length m.memories.length,
             tables := ExternAddr.tables xas ++ List.range' s.tables.length
              (min m.tables.length refsT.length),
             funcs := ExternAddr.funcs xas ++
              (List.range m.funcs.length).map (s.funcs.length + ·),
             datas := List.range' s.datas.length m.data.length,
             elems := List.range' s.elems.length (min m.elems.length refsE.length),
             exports := xi }) :
    allocModule? s m xas valsG refsT refsE = some (
      { s with
        tags := s.tags ++ tagTypes.map TagInst.mk,
        globals := s.globals ++
          ((m.globals.map fun g => (⟨g.type.mutability,
            (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩ : CGlobalType)).zip
            valsG).map (fun p => ⟨p.1, p.2⟩),
        mems := s.mems ++ m.memories.map fun m =>
          ⟨m, ByteArray.mk (Array.replicate (m.limits.min.val * Execution.Memory.pageSize) 0)⟩,
        tables := s.tables ++
          ((m.tables.map fun t => (⟨t.type.address, t.type.limits,
            (liftRef t.type.element).substAll ((allocTypes m.types).map .dt)⟩ : CTableType)).zip
            refsT).map (fun p => ⟨p.1, List.replicate p.1.limits.min.val p.2⟩),
        datas := s.datas ++ (m.data.map Data.bytes).map DataInst.mk,
        elems := s.elems ++
          ((m.elems.map fun e => (liftRef e.type).substAll ((allocTypes m.types).map .dt)).zip
            refsE).map (fun p => ⟨p.1, p.2⟩),
        funcs := s.funcs ++ (funcTypes.zip m.funcs).map fun p => ⟨p.1, mi, .wasm p.2⟩ },
      mi) := by
  subst hmi
  unfold allocModule?
  simp only [Option.bind_eq_bind, ht, hf, Option.bind_some, allocMany_tag_eq, allocMany_global_eq,
    allocMany_mem_eq, allocMany_table_eq, allocMany_data_eq, allocMany_elem_eq]
  simp [hx, allocMany_func_eq, Function.comp_def]

/-! ## Preparation on stores with equal counts -/

/-- A store extended by preparation: every list is appended to, structures and
arrays are replaced. -/
def extend (s : Store H) (T : List TagInst) (G : List GlobalInst) (M : List MemInst)
    (Tb : List TableInst) (D : List DataInst) (E : List ElemInst) (F : List (FuncInst H))
    (Ss : List StructInst) (As : List ArrayInst) : Store H :=
  { s with
    tags := s.tags ++ T, globals := s.globals ++ G, mems := s.mems ++ M,
    tables := s.tables ++ Tb, datas := s.datas ++ D, elems := s.elems ++ E,
    funcs := s.funcs ++ F, structs := Ss, arrays := As }

theorem store_ext {s t : Store H} (h1 : s.tags = t.tags) (h2 : s.globals = t.globals)
    (h3 : s.mems = t.mems) (h4 : s.tables = t.tables) (h5 : s.funcs = t.funcs)
    (h6 : s.datas = t.datas) (h7 : s.elems = t.elems) (h8 : s.structs = t.structs)
    (h9 : s.arrays = t.arrays) (h10 : s.exns = t.exns) : s = t := by
  cases s
  cases t
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

theorem extend_extend (s : Store H) (T G M Tb D E F Ss As T' G' M' Tb' D' E' F' Ss' As') :
    extend (extend s T G M Tb D E F Ss As) T' G' M' Tb' D' E' F' Ss' As' =
      extend s (T ++ T') (G ++ G') (M ++ M') (Tb ++ Tb') (D ++ D') (E ++ E') (F ++ F') Ss' As' := by
  simp [extend, List.append_assoc]

/-- The witnesses of `allocModule?_inv` determine the allocation from the
counts of the store alone. -/
theorem allocModule_congr {X Y X' : Store H} {m : Module} {xas : List ExternAddr}
    {vals : List Val} {rT : List Ref} {rE : List (List Ref)} {mi : ModuleInst}
    (hstat : StoreRelation.Static X Y) (hgl : X.globals.length = Y.globals.length)
    (hfl : X.funcs.length = Y.funcs.length)
    (run : allocModule? X m xas vals rT rE = some (X', mi)) :
    ∃ T G M Tb D E F,
      allocModule? Y m xas vals rT rE = some (extend Y T G M Tb D E F Y.structs Y.arrays, mi) ∧
      X' = extend X T G M Tb D E F X.structs X.arrays := by
  obtain ⟨tagTypes, funcTypes, xi, ht, hf, hx, hmi, hs'⟩ := allocModule?_inv run
  have hx' := hx
  rw [hstat.tags, hstat.mems, hstat.tables, hgl, hfl] at hx'
  have hmi' := hmi
  rw [hstat.tags, hstat.mems, hstat.tables, hgl, hfl, hstat.datas, hstat.elems] at hmi'
  exact ⟨_, _, _, _, _, _, _, allocModule?_of ht hf hx' hmi', hs'⟩

theorem profile_sections {m : Module} (hp : Link.GC.inProfile m = true) :
    m.memories = [] ∧ m.tables = [] ∧ m.tags = [] ∧ m.data = [] ∧ m.elems = [] ∧
      m.start = none := by
  simp only [Link.GC.inProfile, Bool.and_eq_true, List.isEmpty_iff,
    Option.isNone_iff_eq_none] at hp
  exact ⟨hp.1.1.1.1.1.1, hp.1.1.1.1.1.2, hp.1.1.1.1.2, hp.1.1.1.2, hp.1.1.2, hp.1.2⟩

/-- `prepare?` from its initializer run and its allocation, in the linker's profile. -/
theorem prepare_of {s s₁ s' : Store H} {m : Module} {as : List Nat} {f₁ : Frame}
    {values : List Val} {mi : ModuleInst} (hm : Link.GC.inProfile m = true)
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m (imports as)⟩
      (Module.closedGlobalTypes m) (m.globals.map Global.init) = some (s₁, f₁, values))
    (ha : allocModule? s₁ m (imports as) values [] [] = some (s', mi)) :
    prepare? evalConst? s m (imports as) = some (⟨s', { module := mi }, []⟩, none) := by
  obtain ⟨_, ht, _, hd, he, hs⟩ := profile_sections hm
  simp only [Module.closedGlobalTypes] at hg
  unfold prepare?
  simp [ht, hd, he, hs, evalExprs?, evalExprss?, hg, ha, expression]

/-- **Preparation on stores with equal counts, structures and arrays** appends the
same instances to both. -/
theorem prepare_congr {X Y : Store H} {m : Module} {as : List Nat} {cs : Store H} {cf : Frame}
    {cc : List Admin} {st : Option FuncIdx} (hm : Link.GC.inProfile m = true)
    (hp : prepare? evalConst? X m (imports as) = some (⟨cs, cf, cc⟩, st))
    (hstat : StoreRelation.Static X Y) (hs : X.structs = Y.structs) (ha : X.arrays = Y.arrays)
    (hgl : X.globals.length = Y.globals.length) (hfl : X.funcs.length = Y.funcs.length) :
    ∃ T G M Tb D E F Ss As,
      prepare? evalConst? Y m (imports as) =
        some (⟨extend Y T G M Tb D E F Ss As, cf, cc⟩, st) ∧
      cs = extend X T G M Tb D E F Ss As := by
  obtain ⟨X₁, f₁, values, hg, halloc, hloc, hcode, hst⟩ := prepare_allocation hm hp
  dsimp only at halloc hloc hcode
  subst hcode hst
  have hinit : ModuleInst.initial X m (imports as) = ModuleInst.initial Y m (imports as) := by
    simp only [ModuleInst.initial, hfl]
  have hag : Agree X Y ⟨[], ModuleInst.initial X m (imports as)⟩ := by
    intro a h
    simp [ModuleInst.initial, imports_globals] at h
  obtain ⟨Y₁, hgY, ⟨hs₁, ha₁⟩⟩ := evalGlobals_congr hg ⟨hs, ha⟩ hgl hag
  rw [hinit] at hgY
  obtain ⟨hXg, hXf, -⟩ := evalGlobals?_shape hg
  obtain ⟨hYg, hYf, -⟩ := evalGlobals?_shape hgY
  have sX := StoreRelation.evalGlobals_static hg
  have sY := StoreRelation.evalGlobals_static hgY
  have hstat₁ : StoreRelation.Static X₁ Y₁ := (sX.symm.trans hstat).trans sY
  have hgl₁ : X₁.globals.length = Y₁.globals.length := by
    rw [hXg, hYg, List.length_append, List.length_append, hgl]
  have hfl₁ : X₁.funcs.length = Y₁.funcs.length := by rw [hXf, hYf, hfl]
  obtain ⟨T, G, M, Tb, D, E, F, hY', hX'⟩ := allocModule_congr hstat₁ hgl₁ hfl₁ halloc
  have eX₁ : X₁ = extend X [] (List.zipWith GlobalInst.mk (Module.closedGlobalTypes m) values)
      [] [] [] [] [] X₁.structs X₁.arrays :=
    store_ext (by simp [extend, sX.tags]) (by simp [extend, hXg]) (by simp [extend, sX.mems])
      (by simp [extend, sX.tables]) (by simp [extend, hXf]) (by simp [extend, sX.datas])
      (by simp [extend, sX.elems]) (by simp [extend]) (by simp [extend])
      (by simp [extend, sX.exns])
  have eY₁ : Y₁ = extend Y [] (List.zipWith GlobalInst.mk (Module.closedGlobalTypes m) values)
      [] [] [] [] [] X₁.structs X₁.arrays :=
    store_ext (by simp [extend, sY.tags]) (by simp [extend, hYg]) (by simp [extend, sY.mems])
      (by simp [extend, sY.tables]) (by simp [extend, hYf]) (by simp [extend, sY.datas])
      (by simp [extend, sY.elems]) (by simp [extend, hs₁]) (by simp [extend, ha₁])
      (by simp [extend, sY.exns])
  refine ⟨[] ++ T, List.zipWith GlobalInst.mk (Module.closedGlobalTypes m) values ++ G,
    [] ++ M, [] ++ Tb, [] ++ D, [] ++ E, [] ++ F, X₁.structs, X₁.arrays, ?_, ?_⟩
  · rw [prepare_of hm hgY hY']
    obtain ⟨cl, cm⟩ := cf
    dsimp only at hloc ⊢
    subst hloc
    rw [eY₁, extend_extend]
    simp [extend]
  · rw [hX', eX₁, extend_extend]

/-! ## Links survive instantiating the same module -/

theorem forall₂_function_refl : ∀ (F : List (FuncInst H)),
    List.Forall₂ StoreRelation.Function F F
  | [] => .nil
  | fi :: F => .cons (.same fi) (forall₂_function_refl F)

/-- A bijection fixing every address from `n` on maps addresses below `n` below `n`. -/
theorem perm_lt {p : Nat ≃ Nat} {n : Nat} (fix : ∀ a, n ≤ a → p a = a) {a : Nat}
    (ha : a < n) : p a < n := by
  by_contra hge
  have h1 : p (p a) = p a := fix _ (Nat.le_of_not_lt hge)
  have h2 : p a = a := p.injective h1
  omega

theorem lookup_append {α : Type} {p : Nat ≃ Nat} {A B G : List α}
    (h : GlobalPermutation.Lookup p A B) (fix : ∀ a, A.length ≤ a → p a = a)
    (len : A.length = B.length) : GlobalPermutation.Lookup p (A ++ G) (B ++ G) := by
  intro a
  by_cases ha : a < A.length
  · have hp := perm_lt fix ha
    rw [List.getElem?_append_left (by omega), List.getElem?_append_left ha, h a]
  · rw [fix a (by omega), List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega), len]


theorem forall₂_append' {α β : Type} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β} {c : List α} {d : List β},
      List.Forall₂ R a b → List.Forall₂ R c d → List.Forall₂ R (a ++ c) (b ++ d)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hab hrest, h => .cons hab (forall₂_append' hrest h)

theorem mem_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ y ∈ l', ∃ x ∈ l, f x = some y
  | [], l', h, y, hy => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp at hy
  | a :: l, l', h, y, hy => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨a, by simp, hb⟩
    · obtain ⟨x, hx, hfx⟩ := mem_of_mapM hbs y hy
      exact ⟨x, by simp [hx], hfx⟩

/-- What preparation installs: new globals above the old ones, exports of those
globals, and wasm functions with the new module instance. -/
theorem prepared_facts {X : Store H} {m : Module} {as : List Nat} {cs : Store H} {cf : Frame}
    {cc : List Admin} {st : Option FuncIdx} (hm : Link.GC.inProfile m = true)
    (hp : prepare? evalConst? X m (imports as) = some (⟨cs, cf, cc⟩, st)) :
    (∀ a ∈ cf.module.globals, X.globals.length ≤ a) ∧
    (∀ xi ∈ cf.module.exports, ∀ a, xi.addr = .global a → a ∈ cf.module.globals) ∧
    (∀ fi ∈ cs.funcs.drop X.funcs.length, fi.module = cf.module ∧ ∃ code, fi.code = .wasm code) := by
  obtain ⟨X₁, f₁, values, functionTypes, hg, ha, hb⟩ := prepare?_gc_bindings hm hp
  refine ⟨?_, ?_, ?_⟩
  · intro a h
    have hglob : cf.module.globals =
        addresses (X.globals.length + m.globals.length) m.globals.length := hb.globals
    rw [hglob] at h
    simp only [addresses, List.mem_map, List.mem_range] at h
    obtain ⟨i, -, rfl⟩ := h
    omega
  · intro xi hxi a hax
    have ha' : allocModule? X₁ m (imports as) values [] [] = some (cs, cf.module) := ha
    obtain ⟨tagTypes, funcTypes, xs, -, -, hx, hmi, -⟩ := allocModule?_inv ha'
    rw [hmi] at hxi ⊢
    obtain ⟨e, -, he⟩ := mem_of_mapM hx xi hxi
    have hspec := (allocExport?_spec he).2
    rw [hax] at hspec
    simpa using hspec
  · intro fi hfi
    have hfun : cs.funcs = X.funcs ++ functionInstances cf.module functionTypes m.funcs :=
      hb.store_functions
    rw [hfun, List.drop_left] at hfi
    simp only [functionInstances, List.mem_map] at hfi
    obtain ⟨⟨d, fn⟩, -, rfl⟩ := hfi
    exact ⟨rfl, fn, rfl⟩

theorem moduleView_fixed {p : Nat ≃ Nat} {mi : ModuleInst} (hg : ∀ a ∈ mi.globals, p a = a)
    (hx : ∀ xi ∈ mi.exports, ∀ a, xi.addr = .global a → a ∈ mi.globals) :
    GlobalPermutation.moduleView p mi = mi := by
  have h1 : mi.globals.map p = mi.globals :=
    (List.map_congr_left (fun a ha => (hg a ha : p a = id a))).trans (List.map_id _)
  have h2 : mi.exports.map (fun e => { e with addr := GlobalPermutation.external p e.addr }) =
      mi.exports := by
    refine (List.map_congr_left (g := id) ?_).trans (List.map_id _)
    intro e he
    rcases e with ⟨name, addr⟩
    cases addr with
    | global a =>
      simp only [GlobalPermutation.external, id_eq]
      rw [hg a (hx _ he a rfl)]
    | _ => rfl
  unfold GlobalPermutation.moduleView
  rw [h1, h2]

theorem forall₂_externAddrOk {X Y : Store H}
    (htag : ∀ a : Nat, X.funcs[a]?.map FuncInst.type = Y.funcs[a]?.map FuncInst.type) :
    ∀ {as : List Nat} {xts : List CExternType},
      List.Forall₂ (ExternAddrOk X) (imports as) xts → List.Forall₂ (ExternAddrOk Y) (imports as) xts
  | [], _, h => by
    simp only [imports, List.map_nil] at h ⊢
    cases h
    exact .nil
  | a :: as, _, h => by
    simp only [imports, List.map_cons] at h ⊢
    cases h with
    | cons h t => exact .cons (externAddrOk_func (htag a) h) (forall₂_externAddrOk htag t)

/-- Validity of an instantiation, with typed function imports. -/
def Valid (X : Store H) (m : Module) (as : List Nat) : Prop :=
  ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk X) (imports as) xtI

theorem Link.valid {X Y : Store H} (hl : Link X Y) {m : Module} {as : List Nat}
    (hv : Valid X m as) : Valid Y m as := by
  obtain ⟨xtE, xtI, hm, hx⟩ := hv
  exact ⟨xtE, xtI, hm, forall₂_externAddrOk hl.tag_lookup hx⟩

theorem Chain.valid {X Y : Store H} (hc : Chain X Y) {m : Module} {as : List Nat}
    (hv : Valid X m as) : Valid Y m as := by
  obtain ⟨xtE, xtI, hm, hx⟩ := hv
  exact ⟨xtE, xtI, hm, forall₂_externAddrOk hc.tag_lookup hx⟩

/-- A valid instantiation from a valid store gives a valid store. -/
theorem prepare_storeOk {X : Store H} {m : Module} {as : List Nat} {cs : Store H} {cf : Frame}
    {cc : List Admin} {st : Option FuncIdx} (ok : StoreOk X) (hv : Valid X m as)
    (hp : prepare? evalConst? X m (imports as) = some (⟨cs, cf, cc⟩, st)) : StoreOk cs := by
  have hI : Instantiate (Profile.spec false {}) SingleThreaded.divHost X m (imports as)
      (Config.withStart ⟨cs, cf, cc⟩ st) := (prepare?_iff hv).mp (by rw [hp]; rfl)
  have hok := Instantiate.ok SingleThreaded.divHost_ok ok hI
  have := hok.choose_spec.1.1
  cases st <;> exact this

/-- **A link survives instantiating the same module on both ends.** -/
theorem Link.prepare {X Y : Store H} (hl : Link X Y) {m : Module} {as : List Nat}
    {cs : Store H} {cf : Frame} {cc : List Admin} {st : Option FuncIdx}
    (hm : Link.GC.inProfile m = true)
    (hp : prepare? evalConst? X m (imports as) = some (⟨cs, cf, cc⟩, st)) (hv : Valid X m as) :
    ∃ cs', prepare? evalConst? Y m (imports as) = some (⟨cs', cf, cc⟩, st) ∧ Link cs cs' := by
  cases hl with
  | related h ok =>
    obtain ⟨T, G, M, Tb, D, E, F, Ss, As, hY, hX⟩ := prepare_congr hm hp
      ⟨h.tags, h.mems, h.tables, h.datas, h.elems, h.exns⟩ h.structs h.arrays
      (congrArg List.length h.globals) h.functions.length_eq
    refine ⟨_, hY, .related ?_ (prepare_storeOk ok hv hp)⟩
    rw [hX]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, by simp [extend], by simp [extend], ?_⟩, ?_⟩
    · simp [extend, h.tags]
    · simp [extend, h.globals]
    · simp [extend, h.mems]
    · simp [extend, h.tables]
    · simp [extend, h.datas]
    · simp [extend, h.elems]
    · simp [extend, h.exns]
    · exact forall₂_append' h.functions (forall₂_function_refl F)
  | @renamed p h fix len =>
    obtain ⟨T, G, M, Tb, D, E, F, Ss, As, hY, hX⟩ := prepare_congr hm hp
      ⟨h.tags, h.mems, h.tables, h.datas, h.elems, h.exns⟩ h.structs h.arrays len
      (by rw [h.functions, List.length_map])
    obtain ⟨hglob, hexp, hfun⟩ := prepared_facts hm hp
    have hF : F.map (GlobalPermutation.function p) = F := by
      have hF' : F = cs.funcs.drop X.funcs.length := by
        rw [hX]
        simp [extend]
      refine (List.map_congr_left (g := id) ?_).trans (List.map_id _)
      intro fi hfi
      obtain ⟨hmod, code, hcode⟩ := hfun fi (hF' ▸ hfi)
      rcases fi with ⟨d, md, c⟩
      simp only at hmod hcode
      subst hmod hcode
      simp only [GlobalPermutation.function, id_eq]
      rw [moduleView_fixed (fun a ha => fix a (hglob a ha)) hexp]
    have hcsg : cs.globals.length = X.globals.length + G.length := by
      rw [hX]
      simp [extend]
    refine ⟨_, hY, .renamed (p := p) ?_ ?_ ?_⟩
    · rw [hX]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp [extend], by simp [extend], ?_⟩
      · exact lookup_append h.globals fix len
      · simp only [extend, List.map_append, h.functions, hF]
      · simp [extend, h.tags]
      · simp [extend, h.mems]
      · simp [extend, h.tables]
      · simp [extend, h.datas]
      · simp [extend, h.elems]
      · simp [extend, h.exns]
    · intro a ha
      exact fix a (by omega)
    · rw [hcsg]
      simp [extend, len]

theorem Link.prepare_back {X Y : Store H} (hl : Link X Y) {m : Module} {as : List Nat}
    {cs' : Store H} {cf : Frame} {cc : List Admin} {st : Option FuncIdx}
    (hm : Link.GC.inProfile m = true)
    (hp : prepare? evalConst? Y m (imports as) = some (⟨cs', cf, cc⟩, st)) :
    ∃ cs, prepare? evalConst? X m (imports as) = some (⟨cs, cf, cc⟩, st) := by
  cases hl with
  | related h _ =>
    obtain ⟨_, _, _, _, _, _, _, _, _, hX, -⟩ := prepare_congr hm hp
      ⟨h.tags.symm, h.mems.symm, h.tables.symm, h.datas.symm, h.elems.symm, h.exns.symm⟩
      h.structs.symm h.arrays.symm (congrArg List.length h.globals).symm
      h.functions.length_eq.symm
    exact ⟨_, hX⟩
  | renamed h _ len =>
    obtain ⟨_, _, _, _, _, _, _, _, _, hX, -⟩ := prepare_congr hm hp
      ⟨h.tags.symm, h.mems.symm, h.tables.symm, h.datas.symm, h.elems.symm, h.exns.symm⟩
      h.structs.symm h.arrays.symm len.symm (by rw [h.functions, List.length_map])
    exact ⟨_, hX⟩

/-- **A chain survives instantiating the same module on both ends.** -/
theorem Chain.prepare {m : Module} {as : List Nat} (hm : Link.GC.inProfile m = true) :
    ∀ {X Y : Store H}, Chain X Y →
      ∀ {cs : Store H} {cf : Frame} {cc : List Admin} {st : Option FuncIdx},
        prepare? evalConst? X m (imports as) = some (⟨cs, cf, cc⟩, st) → Valid X m as →
        ∃ cs', prepare? evalConst? Y m (imports as) = some (⟨cs', cf, cc⟩, st) ∧ Chain cs cs'
  | _, _, .refl _, cs, _, _, _, hp, _ => ⟨cs, hp, .refl _⟩
  | _, _, .cons hl hc, _, _, _, _, hp, hv => by
    obtain ⟨cs₁, hp₁, hl₁⟩ := hl.prepare hm hp hv
    obtain ⟨cs₂, hp₂, hc₂⟩ := Chain.prepare hm hc hp₁ (hl.valid hv)
    exact ⟨cs₂, hp₂, .cons hl₁ hc₂⟩

theorem Chain.prepare_back {m : Module} {as : List Nat} (hm : Link.GC.inProfile m = true) :
    ∀ {X Y : Store H}, Chain X Y →
      ∀ {cs' : Store H} {cf : Frame} {cc : List Admin} {st : Option FuncIdx},
        prepare? evalConst? Y m (imports as) = some (⟨cs', cf, cc⟩, st) →
        ∃ cs, prepare? evalConst? X m (imports as) = some (⟨cs, cf, cc⟩, st)
  | _, _, .refl _, cs', _, _, _, hp => ⟨cs', hp⟩
  | _, _, .cons hl hc, _, _, _, _, hp => by
    obtain ⟨cs₁, hp₁⟩ := Chain.prepare_back hm hc hp
    exact hl.prepare_back hm hp₁

end Silmaril.Wasm.Binaryen.MergeChain
