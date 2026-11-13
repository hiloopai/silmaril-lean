module

public import Silmaril.Wasm.JcoTool.Adaptor.Defs
public import Silmaril.Wasm.JcoTool.New.Thms
public import Silmaril.Wasm.JcoTool.Emit.Thms
public import Silmaril.Wasm.Component.Binary.Thms
public import Silmaril.Wasm.Jco.Wrap.Thms
public import Silmaril.Wasm.Jco.Real.ValidRange.Thms
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound

/-!
# The correctness theorem of `wasm-jco new --adaptor`

**`newAdaptor_correct`**: if adaptor mode succeeds (`newAdaptor core w alloc = .ok o`), then

1. the metadata is `Meta.ofWorld w alloc`;
2. the module exports the allocator at `(i32, i32) -> i32` and each world function at its
   C-convention core type (`calleeCore`), and imports nothing;
3. the adaptor bytes encode `(adaptorLime md).toCore` in the Core binary grammar (silmaril's
   `encodeModule?_sound`), and they are the second core module of the output, which the
   verified component parser reads back;
4. that adaptor validates whenever the world's names are distinct and it has fewer than
   `2^31` functions (`Jco.adaptorLime_valid_of_lt`);
5. the wrapper `wrap md` of jco part (a), whose adaptor `adaptorLime md` encodes, behaves at
   the world as the module under the C convention, for every conforming core instance
   (`Jco.wrap_correct`).

Item 5 is about the memory model's `wrap md`; that its adaptor programs (`adaptorOf md`) run as
the Lime1 code `adaptorLime md` is the forward agreement of `Silmaril.Wasm.Jco.Real`
(`invoke_agree` on the fragment `wrap_adaptor_frag`), not re-proved here, and the canonical
lifts of the output are read by wasmtime, which the tests run (`tools/wasm-jco/tests`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Adaptor

open Silmaril.Wasm.Wit.Binary (World Func)
open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component (CoreFuncTy)
open Silmaril.Wasm.Jco (Meta Sig CoreInst PVal)
open New (bind_ok require_ok expectExport_ok)

theorem forM_ok {α : Type} {f : α → Except String Unit} :
    ∀ {l : List α} {u : Unit}, l.forM f = .ok u → ∀ x ∈ l, f x = .ok ()
  | [], _, _, _, hx => nomatch hx
  | a :: l, _, h, x, hx => by
    obtain ⟨⟨⟩, ha, hl⟩ := bind_ok h
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ha
    · exact forM_ok hl x hx'

/-- What the plan of adaptor mode checks. -/
theorem planAdaptor_ok {core : ByteArray} {w : World} {alloc : String} {p : Plan}
    (h : planAdaptor core w alloc = .ok p) :
    Meta.ofWorld w alloc = .ok p.md ∧ Lower.coreMod core = .ok p.mod ∧
      p.mod.imports = [] ∧ New.coreExport? p.mod alloc = some ⟨[ti32, ti32], [ti32]⟩ ∧
      ∀ s ∈ p.md.world, New.coreExport? p.mod s.name = some (calleeCore s) := by
  obtain ⟨md, hmd, h₁⟩ := bind_ok h
  obtain ⟨m, hm, h₂⟩ := bind_ok h₁
  obtain ⟨_, _, h₃⟩ := bind_ok h₂
  obtain ⟨_, hi, h₄⟩ := bind_ok h₃
  obtain ⟨_, _, h₅⟩ := bind_ok h₄
  obtain ⟨_, ha, h₆⟩ := bind_ok h₅
  obtain ⟨_, hw, h₇⟩ := bind_ok h₆
  cases h₇
  have hie : m.imports = [] := List.isEmpty_iff.mp (require_ok hi)
  exact ⟨hmd, (congrFun Silmaril.Wasm.Perf.CoreMod.coreModF_eq core).symm.trans hm, hie,
    expectExport_ok ha, fun s hs => expectExport_ok (forM_ok hw s hs)⟩

theorem adaptorBytes_encodes {md : Meta} {a : ByteArray} (h : adaptorBytes md = .ok a) :
    Silmaril.Wasm.Binary.Core.Encodes a.data.toList (Silmaril.Wasm.Jco.adaptorLime md).toCore := by
  obtain ⟨bs, hbs, h₁⟩ := bind_ok h
  cases h₁
  have e : (⟨bs.toArray⟩ : ByteArray).data.toList = bs := List.toList_toArray
  rw [e]
  exact Silmaril.Wasm.Binaryen.Exe.encodeModule?_sound hbs

theorem emitAdaptor_sections {core a : ByteArray} {p : Plan} {c : XAst}
    (h : emitAdaptor core a p = .ok c) :
    ∃ rest, c.sections = .sec (.coreModule core) :: .sec (.coreModule a) :: rest := by
  obtain ⟨_, _, h₁⟩ := bind_ok h
  cases h₁
  exact ⟨_, rfl⟩

theorem toSections_two {core a : ByteArray} {rest : List XSection} {ss : List Section}
    (h : XSection.toSections (.sec (.coreModule core) :: .sec (.coreModule a) :: rest) = some ss) :
    ss[1]? = some (.coreModule a) := by
  cases hr : XSection.toSections rest with
  | none => simp [XSection.toSections, hr] at h
  | some ss' =>
    have e : ss = .coreModule core :: .coreModule a :: ss' := by
      simpa [XSection.toSections, hr] using h.symm
    rw [e]
    rfl

theorem newAdaptor_steps {core : ByteArray} {w : World} {alloc : String} {o : Out}
    (h : newAdaptor core w alloc = .ok o) :
    planAdaptor core w alloc = .ok o.plan ∧ adaptorBytes o.plan.md = .ok o.adaptor ∧
      ∃ c, emitAdaptor core o.adaptor o.plan = .ok c ∧ c.encode = some o.bytes ∧ o.ast = c.toAst := by
  obtain ⟨p, hp, h₁⟩ := bind_ok h
  obtain ⟨a, ha, h₂⟩ := bind_ok h₁
  obtain ⟨c, hc, h₃⟩ := bind_ok h₂
  obtain ⟨b, hb, h₄⟩ := bind_ok h₃
  cases h₄
  have hb' : c.encode = some b := by
    unfold New.mustEncode at hb
    split at hb
    · cases hb
      assumption
    · cases hb
  exact ⟨hp, ha, c, hc, hb', rfl⟩

/-- The output's syntax: read back by the verified parser, with the adaptor as its second core
module. -/
theorem newAdaptor_parse {core : ByteArray} {w : World} {alloc : String} {o : Out} {a : Ast}
    (h : newAdaptor core w alloc = .ok o) (ha : o.ast = some a) :
    parse o.bytes = .ok a ∧ a.sections[1]? = some (.coreModule o.adaptor) := by
  obtain ⟨_, _, c, hc, he, hast⟩ := newAdaptor_steps h
  have hc' : c.toAst = some a := hast ▸ ha
  have hb : Silmaril.Wasm.Component.Binary.encode a = some o.bytes := by
    rw [← XAst.encode_toAst hc', he]
  obtain ⟨rest, hs⟩ := emitAdaptor_sections hc
  cases hss : XSection.toSections c.sections with
  | none => simp [XAst.toAst, hss] at hc'
  | some ss =>
    have e : a = .mk ss := by simpa [XAst.toAst, hss] using hc'.symm
    refine ⟨Silmaril.Wasm.Component.Binary.parse_encode hb, ?_⟩
    rw [e]
    exact toSections_two (hs ▸ hss)

/-- **The correctness theorem of adaptor mode.** -/
theorem newAdaptor_correct {core : ByteArray} {w : World} {alloc : String} {o : Out}
    (h : newAdaptor core w alloc = .ok o) :
    Meta.ofWorld w alloc = .ok o.plan.md ∧
    (o.plan.mod.imports = [] ∧ New.coreExport? o.plan.mod alloc = some ⟨[ti32, ti32], [ti32]⟩ ∧
      ∀ s ∈ o.plan.md.world, New.coreExport? o.plan.mod s.name = some (calleeCore s)) ∧
    Silmaril.Wasm.Binary.Core.Encodes o.adaptor.data.toList
      (Silmaril.Wasm.Jco.adaptorLime o.plan.md).toCore ∧
    (∀ a, o.ast = some a → parse o.bytes = .ok a ∧ a.sections[1]? = some (.coreModule o.adaptor)) ∧
    ((Silmaril.Wasm.Jco.importNames o.plan.md).Nodup →
      "cabi_realloc" ∉ o.plan.md.world.map (·.name) →
      (∀ s ∈ o.plan.md.world, (Silmaril.Wasm.Jco.flatParams s.params).length + 2 < 2 ^ 32) →
      o.plan.md.world.length < 2 ^ 31 →
      Silmaril.Wasm.Validation.ModuleValid (Silmaril.Wasm.Jco.adaptorLime o.plan.md).toCore) ∧
    (∀ M : CoreInst, o.plan.md.Conforms M → ∀ (name : String) (vs : List PVal),
      (Silmaril.Wasm.Jco.wrap o.plan.md).callExport M name vs = o.plan.md.spec M name vs) := by
  obtain ⟨hp, ha, _⟩ := newAdaptor_steps h
  obtain ⟨hmd, _, hi, hal, hs⟩ := planAdaptor_ok hp
  exact ⟨hmd, ⟨hi, hal, hs⟩, adaptorBytes_encodes ha, fun a hast => newAdaptor_parse h hast,
    fun hn hr hpar hw => Silmaril.Wasm.Jco.Real.adaptorLime_valid_of_lt _ hn hr hpar hw,
    fun M hC name vs => Silmaril.Wasm.Jco.wrap_correct M _ hC name vs⟩

end Silmaril.Wasm.JcoTool.Adaptor
