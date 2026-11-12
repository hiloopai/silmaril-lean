module

public import Silmaril.Raw.Wasm.SpecTec.Wasm.V1.Binary.Instructions
public import Silmaril.Wasm.V1.Modules
public import Silmaril.Encoding

/-! # WebAssembly 1.0 binary format: modules

Transcribed from REC 5.5 (5 December 2019). The module grammar is stated once for
the scalar module record `Scalar.Module E`, parameterized by the expression
grammar `G : Bytes → E → Prop`, because Lime1 changes only the instruction
encodings: it reuses this grammar with its own expressions (see
`Lime1/Binary/Modules.lean`). Sections occur in the 1.0 order
(type, import, function, table, memory, global, export, start, element, code,
data), each optional and possibly empty, with custom sections anywhere; the
function and code sections must have equal lengths (REC 5.5.15).
-/

@[expose] public section

namespace Silmaril.Wasm.Scalar.Binary

open Silmaril.Wasm.Binary

variable {E : Type}

/-- `importdesc` (REC 5.5.5). -/
inductive ImportDesc : Bytes → V1.ImportDesc → Prop where
  | func {b : Bytes} {x : TypeIdx} (h : Index b x) : ImportDesc ([0x00] ++ b) (.func x)
  | table {b : Bytes} {t : V1.TableType} (h : V1.Binary.TableType b t) : ImportDesc ([0x01] ++ b)
      (.table t)
  | memory {b : Bytes} {t : V1.MemoryType} (h : V1.Binary.MemType b t) :
      ImportDesc ([0x02] ++ b) (.memory t)
  | global {b : Bytes} {t : V1.GlobalType} (h : V1.Binary.GlobalType b t) :
      ImportDesc ([0x03] ++ b) (.global t)

/-- `import ::= mod:name nm:name d:importdesc` (REC 5.5.5). -/
inductive Import : Bytes → V1.Import → Prop where
  | mk {b₁ b₂ b₃ : Bytes} {m n : String} {d : V1.ImportDesc} (h₁ : Name b₁ m) (h₂ : Name b₂ n)
      (h₃ : ImportDesc b₃ d) : Import (b₁ ++ b₂ ++ b₃) ⟨m, n, d⟩

/-- `exportdesc` (REC 5.5.10). -/
inductive ExportDesc : Bytes → V1.ExternIdx → Prop where
  | func {b : Bytes} {x : FuncIdx} (h : Index b x) : ExportDesc ([0x00] ++ b) (.func x)
  | table {b : Bytes} {x : TableIdx} (h : Index b x) : ExportDesc ([0x01] ++ b) (.table x)
  | memory {b : Bytes} {x : MemIdx} (h : Index b x) : ExportDesc ([0x02] ++ b) (.memory x)
  | global {b : Bytes} {x : GlobalIdx} (h : Index b x) : ExportDesc ([0x03] ++ b) (.global x)

/-- `export ::= nm:name d:exportdesc` (REC 5.5.10). -/
inductive Export : Bytes → V1.Export → Prop where
  | mk {b b' : Bytes} {n : String} {d : V1.ExternIdx} (h : Name b n) (h' : ExportDesc b' d) :
      Export (b ++ b') ⟨n, d⟩

/-- `global ::= gt:globaltype e:expr` (REC 5.5.9). -/
inductive Global (G : Bytes → E → Prop) : Bytes → Declaration.Global V1.GlobalType E → Prop where
  | mk {b be : Bytes} {gt : V1.GlobalType} {e : E} (h : V1.Binary.GlobalType b gt) (he : G be e) :
      Global G (b ++ be) ⟨gt, e⟩

/-- `elem ::= x:tableidx e:expr y*:vec(funcidx)` (REC 5.5.12). -/
inductive Elem (G : Bytes → E → Prop) : Bytes → Declaration.ActiveElem E → Prop where
  | mk {bx be bys : Bytes} {x : TableIdx} {e : E} {ys : List FuncIdx} (hx : Index bx x)
      (he : G be e) (hy : Vec Index bys ys) : Elem G (bx ++ be ++ bys) ⟨x, e, ys⟩

/-- `locals ::= n:u32 t:valtype ⇒ tⁿ` (REC 5.5.13). -/
inductive Locals : Bytes → List V1.ValType → Prop where
  | mk {bn bt : Bytes} {n : Nat} {t : V1.ValType} (hn : U32 bn n) (ht : V1.Binary.ValType bt t) :
      Locals (bn ++ bt) (List.replicate n t)

/-- `func ::= (t*)*:vec(locals) e:expr ⇒ concat((t*)*), e  (if |concat((t*)*)| < 2³²)`
(REC 5.5.13). -/
inductive Func (G : Bytes → E → Prop) : Bytes → List V1.ValType × E → Prop where
  | mk {bl be : Bytes} {lss : List (List V1.ValType)} {e : E} (hl : Vec Locals bl lss)
      (he : G be e) (hlen : lss.flatten.length < 2 ^ 32) : Func G (bl ++ be) (lss.flatten, e)

/-- `code ::= size:u32 code:func ⇒ code  (if size = ||func||)` (REC 5.5.13). -/
inductive Code (G : Bytes → E → Prop) : Bytes → List V1.ValType × E → Prop where
  | mk {bl c : Bytes} {len : Nat} {code : List V1.ValType × E} (hl : U32 bl len)
      (hlen : len = c.length) (h : Func G c code) : Code G (bl ++ c) code

/-- `data ::= x:memidx e:expr b*:vec(byte)` (REC 5.5.14). -/
inductive Data (G : Bytes → E → Prop) : Bytes → Declaration.ActiveData E → Prop where
  | mk {bx be bb : Bytes} {x : MemIdx} {e : E} {bs : List UInt8} (hx : Index bx x) (he : G be e)
      (hb : ByteVec bb bs) : Data G (bx ++ be ++ bb) ⟨x, e, ⟨bs.toArray⟩⟩

/-- The functions of a module from its function and code sections (REC 5.5.15:
`funcⁿ[i] = {type typeidxⁿ[i], locals tᵢ*, body eᵢ}`). -/
def zipFuncs (xs : List TypeIdx) (codes : List (List V1.ValType × E)) :
    List (Declaration.Func V1.ValType E) :=
  List.zipWith (fun x c => ⟨x, c.1, c.2⟩) xs codes

/-- `module` (REC 5.5.15). -/
inductive Module (G : Bytes → E → Prop) : Bytes → Scalar.Module E → Prop where
  | mk {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ : Bytes}
      {bty bim bfn btb bme bgl bex bst bel bco bda : Bytes}
      {types : List V1.FuncType} {imports : List V1.Import} {typeidxs : List TypeIdx}
      {tables : List V1.TableType} {mems : List V1.MemoryType}
      {globals : List (Declaration.Global V1.GlobalType E)} {exports : List V1.Export}
      {start : Option FuncIdx} {elems : List (Declaration.ActiveElem E)}
      {codes : List (List V1.ValType × E)} {data : List (Declaration.ActiveData E)}
      (h₀ : Customs c₀) (hty : Section 1 (Vec V1.Binary.FuncType) bty types)
      (h₁ : Customs c₁) (him : Section 2 (Vec Import) bim imports)
      (h₂ : Customs c₂) (hfn : Section 3 (Vec (Index (k := .type_))) bfn typeidxs)
      (h₃ : Customs c₃) (htb : Section 4 (Vec V1.Binary.TableType) btb tables)
      (h₄ : Customs c₄) (hme : Section 5 (Vec V1.Binary.MemType) bme mems)
      (h₅ : Customs c₅) (hgl : Section 6 (Vec (Global G)) bgl globals)
      (h₆ : Customs c₆) (hex : Section 7 (Vec Export) bex exports)
      (h₇ : Customs c₇) (hst : StartSec bst start)
      (h₈ : Customs c₈) (hel : Section 9 (Vec (Elem G)) bel elems)
      (h₉ : Customs c₉) (hco : Section 10 (Vec (Code G)) bco codes)
      (h₁₀ : Customs c₁₀) (hda : Section 11 (Vec (Data G)) bda data)
      (h₁₁ : Customs c₁₁)
      (hfuncs : typeidxs.length = codes.length) :
      Module G (magic ++ version ++ c₀ ++ bty ++ c₁ ++ bim ++ c₂ ++ bfn ++ c₃ ++ btb ++
          c₄ ++ bme ++ c₅ ++ bgl ++ c₆ ++ bex ++ c₇ ++ bst ++ c₈ ++ bel ++ c₉ ++ bco ++
          c₁₀ ++ bda ++ c₁₁)
        { types, imports, funcs := zipFuncs typeidxs codes, globals, tables, memories := mems,
          elems, data, start, exports }

/-! ## Mapping expressions through the grammar -/

section Map

variable {α β E' : Type}

theorem seq_map {G : Bytes → α → Prop} {G' : Bytes → β → Prop} (f : α → β)
    (hf : ∀ {b a}, G b a → G' b (f a)) {b : Bytes} {l : List α} (h : Seq G b l) :
    Seq G' b (l.map f) := by
  induction h with
  | nil => exact .nil
  | cons hb _ ih => exact .cons (hf hb) ih

theorem vec_map {G : Bytes → α → Prop} {G' : Bytes → β → Prop} (f : α → β)
    (hf : ∀ {b a}, G b a → G' b (f a)) {b : Bytes} {l : List α} (h : Vec G b l) :
    Vec G' b (l.map f) := by
  cases h with
  | mk hn hs => exact .mk (by rwa [List.length_map]) (seq_map f (fun h => hf h) hs)

theorem section_map {N : UInt8} {G : Bytes → List α → Prop} {G' : Bytes → List β → Prop}
    (f : α → β) (hf : ∀ {b l}, G b l → G' b (l.map f)) {b : Bytes} {l : List α}
    (h : Section N G b l) : Section N G' b (l.map f) := by
  cases h with
  | mk hl hlen hc => exact .mk hl hlen (hf hc)
  | empty => exact .empty

theorem Global.map {G : Bytes → E → Prop} {G' : Bytes → E' → Prop} (f : E → E')
    (hf : ∀ {b e}, G b e → G' b (f e)) {b : Bytes} {g : Declaration.Global V1.GlobalType E}
    (h : Global G b g) : Global G' b (g.mapInit f) := by
  cases h with
  | mk h he => exact .mk h (hf he)

theorem Elem.map {G : Bytes → E → Prop} {G' : Bytes → E' → Prop} (f : E → E')
    (hf : ∀ {b e}, G b e → G' b (f e)) {b : Bytes} {e : Declaration.ActiveElem E}
    (h : Elem G b e) : Elem G' b ⟨e.table, f e.offset, e.init⟩ := by
  cases h with
  | mk hx he hy => exact .mk hx (hf he) hy

theorem Data.map {G : Bytes → E → Prop} {G' : Bytes → E' → Prop} (f : E → E')
    (hf : ∀ {b e}, G b e → G' b (f e)) {b : Bytes} {d : Declaration.ActiveData E}
    (h : Data G b d) : Data G' b ⟨d.memory, f d.offset, d.bytes⟩ := by
  cases h with
  | mk hx he hb => exact .mk hx (hf he) hb

theorem Func.map {G : Bytes → E → Prop} {G' : Bytes → E' → Prop} (f : E → E')
    (hf : ∀ {b e}, G b e → G' b (f e)) {b : Bytes} {c : List V1.ValType × E}
    (h : Func G b c) : Func G' b (c.1, f c.2) := by
  cases h with
  | mk hl he hlen => exact .mk hl (hf he) hlen

theorem Code.map {G : Bytes → E → Prop} {G' : Bytes → E' → Prop} (f : E → E')
    (hf : ∀ {b e}, G b e → G' b (f e)) {b : Bytes} {c : List V1.ValType × E}
    (h : Code G b c) : Code G' b (c.1, f c.2) := by
  cases h with
  | mk hl hlen h => exact .mk hl hlen (Func.map f (fun h => hf h) h)

theorem zipFuncs_map (f : E → E') (xs : List TypeIdx) (codes : List (List V1.ValType × E)) :
    (zipFuncs xs codes).map (Declaration.Func.mapBody f) =
      zipFuncs xs (codes.map fun c => (c.1, f c.2)) := by
  induction xs generalizing codes with
  | nil => rfl
  | cons x xs ih =>
    cases codes with
    | nil => rfl
    | cons c codes =>
      simp only [zipFuncs, List.zipWith_cons_cons, List.map_cons] at ih ⊢
      rw [ih]
      rfl

end Map

/-! ## Prefix-freeness of the module productions -/

section PrefixFree

variable {α β : Type}

theorem pf_append {G₁ : Bytes → α → Prop} {G₂ : Bytes → β → Prop} (h₁ : PrefixFree G₁)
    (h₂ : PrefixFree G₂) {b₁ b₂ b₁' b₂' r r' : Bytes} {a₁ a₁' : α} {a₂ a₂' : β}
    (g₁ : G₁ b₁ a₁) (g₂ : G₂ b₂ a₂) (g₁' : G₁ b₁' a₁') (g₂' : G₂ b₂' a₂')
    (h : b₁ ++ b₂ ++ r = b₁' ++ b₂' ++ r') : b₁ = b₁' ∧ b₂ = b₂' ∧ a₁ = a₁' ∧ a₂ = a₂' := by
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨rfl, rfl⟩ := h₁ g₁ g₁' h
  obtain ⟨rfl, rfl⟩ := h₂ g₂ g₂' (List.append_cancel_left h)
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem tag_eq {t t' : UInt8} {b b' r r' : Bytes} (h : [t] ++ b ++ r = [t'] ++ b' ++ r') :
    t = t' ∧ b ++ r = b' ++ r' := by
  simp only [List.cons_append, List.cons.injEq] at h
  exact h

theorem memType_prefixFree : PrefixFree V1.Binary.MemType := by
  intro _ _ r r' _ _ ha ha' h
  cases ha with
  | mk ha =>
    cases ha' with
    | mk ha' =>
      obtain ⟨rfl, rfl⟩ := V1.Binary.Limits.prefixFree ha ha' h
      exact ⟨rfl, rfl⟩

theorem ImportDesc.prefixFree : PrefixFree ImportDesc := by
  intro _ _ r r' _ _ ha ha' h
  rcases ha with ⟨h₁⟩ | ⟨h₁⟩ | ⟨h₁⟩ | ⟨h₁⟩ <;> rcases ha' with ⟨h₂⟩ | ⟨h₂⟩ | ⟨h₂⟩ | ⟨h₂⟩ <;>
    obtain ⟨ht, h⟩ := tag_eq h <;>
    first
    | exact absurd ht (by decide)
    | (obtain ⟨rfl, rfl⟩ := Index.prefixFree h₁ h₂ h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨rfl, rfl⟩ := V1.Binary.TableType.prefixFree h₁ h₂ h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨rfl, rfl⟩ := memType_prefixFree h₁ h₂ h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨rfl, rfl⟩ := V1.Binary.GlobalType.prefixFree h₁ h₂ h; exact ⟨rfl, rfl⟩)

theorem Import.prefixFree : PrefixFree Import := by
  intro _ _ r r' _ _ ha ha' h
  cases ha with
  | mk h₁ h₂ h₃ =>
    cases ha' with
    | mk h₁' h₂' h₃' =>
      rw [List.append_assoc _ _ r, List.append_assoc _ _ r'] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := pf_append Name.prefixFree Name.prefixFree h₁ h₂ h₁' h₂' h
      obtain ⟨rfl, rfl⟩ := ImportDesc.prefixFree h₃ h₃' (List.append_cancel_left h)
      exact ⟨rfl, rfl⟩

theorem ExportDesc.prefixFree : PrefixFree ExportDesc := by
  intro _ _ r r' _ _ ha ha' h
  rcases ha with ⟨h₁⟩ | ⟨h₁⟩ | ⟨h₁⟩ | ⟨h₁⟩ <;> rcases ha' with ⟨h₂⟩ | ⟨h₂⟩ | ⟨h₂⟩ | ⟨h₂⟩ <;>
    obtain ⟨ht, h⟩ := tag_eq h <;>
    first
    | exact absurd ht (by decide)
    | (obtain ⟨rfl, rfl⟩ := Index.prefixFree h₁ h₂ h; exact ⟨rfl, rfl⟩)

theorem Export.prefixFree : PrefixFree Export := by
  intro _ _ r r' _ _ ha ha' h
  cases ha with
  | mk h₁ h₂ =>
    cases ha' with
    | mk h₁' h₂' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ :=
        pf_append Name.prefixFree ExportDesc.prefixFree h₁ h₂ h₁' h₂' h
      exact ⟨rfl, rfl⟩

theorem Global.prefixFree {G : Bytes → E → Prop} (hG : PrefixFree G) :
    PrefixFree (Global G) := by
  intro _ _ r r' _ _ ha ha' h
  cases ha with
  | mk h₁ h₂ =>
    cases ha' with
    | mk h₁' h₂' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ :=
        pf_append V1.Binary.GlobalType.prefixFree hG h₁ h₂ h₁' h₂' h
      exact ⟨rfl, rfl⟩

theorem Elem.prefixFree {G : Bytes → E → Prop} (hG : PrefixFree G) : PrefixFree (Elem G) := by
  intro _ _ r r' _ _ ha ha' h
  cases ha with
  | mk h₁ h₂ h₃ =>
    cases ha' with
    | mk h₁' h₂' h₃' =>
      rw [List.append_assoc _ _ r, List.append_assoc _ _ r'] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := pf_append Index.prefixFree hG h₁ h₂ h₁' h₂' h
      obtain ⟨rfl, rfl⟩ := Vec.prefixFree Index.prefixFree h₃ h₃' (List.append_cancel_left h)
      exact ⟨rfl, rfl⟩

theorem Data.prefixFree {G : Bytes → E → Prop} (hG : PrefixFree G) : PrefixFree (Data G) := by
  intro _ _ r r' _ _ ha ha' h
  cases ha with
  | mk h₁ h₂ h₃ =>
    cases ha' with
    | mk h₁' h₂' h₃' =>
      rw [List.append_assoc _ _ r, List.append_assoc _ _ r'] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := pf_append Index.prefixFree hG h₁ h₂ h₁' h₂' h
      obtain ⟨rfl, rfl⟩ := Vec.prefixFree Byte.prefixFree h₃ h₃' (List.append_cancel_left h)
      exact ⟨rfl, rfl⟩

theorem Locals.prefixFree : PrefixFree Locals := by
  intro _ _ r r' _ _ ha ha' h
  cases ha with
  | mk h₁ h₂ =>
    cases ha' with
    | mk h₁' h₂' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ :=
        pf_append (UN.prefixFree 32) V1.Binary.ValType.prefixFree h₁ h₂ h₁' h₂' h
      exact ⟨rfl, rfl⟩

theorem Func.prefixFree {G : Bytes → E → Prop} (hG : PrefixFree G) : PrefixFree (Func G) := by
  intro _ _ r r' _ _ ha ha' h
  cases ha with
  | mk h₁ h₂ _ =>
    cases ha' with
    | mk h₁' h₂' _ =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ :=
        pf_append (Vec.prefixFree Locals.prefixFree) hG h₁ h₂ h₁' h₂' h
      exact ⟨rfl, rfl⟩

theorem Code.prefixFree {G : Bytes → E → Prop} (hG : PrefixFree G) : PrefixFree (Code G) := by
  intro _ _ r r' _ _ ha ha' h
  cases ha with
  | mk h₁ _ h₂ =>
    cases ha' with
    | mk h₁' _ h₂' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ :=
        pf_append (UN.prefixFree 32) (Func.prefixFree hG) h₁ h₂ h₁' h₂' h
      exact ⟨rfl, rfl⟩

theorem Start.functional : Functional Start := by
  intro _ _ _ ha ha'
  cases ha with
  | mk h =>
    cases ha' with
    | mk h' =>
      obtain ⟨-, rfl⟩ := Index.prefixFree (r := []) (r' := []) h h' rfl
      rfl

end PrefixFree

/-! ## Raw sections

Every section, custom or not, is `N:byte len:u32 c:byte^len`. A module body is a
sequence of such raw sections, determined by its bytes; the abstract syntax is
read off the non-custom ones, whose ids are pairwise distinct. -/

section Raw

variable {α : Type}

/-- A section with id `p.1` and contents `p.2`, uninterpreted. -/
def RawSec (b : Bytes) (p : UInt8 × Bytes) : Prop :=
  ∃ lb, U32 lb p.2.length ∧ b = [p.1] ++ lb ++ p.2

theorem RawSec.prefixFree : PrefixFree RawSec := by
  rintro _ _ r r' ⟨n, c⟩ ⟨n', c'⟩ ⟨lb, hl, rfl⟩ ⟨lb', hl', rfl⟩ h
  have h : [n] ++ lb ++ (c ++ r) = [n'] ++ lb' ++ (c' ++ r') := by
    simpa only [List.append_assoc] using h
  obtain ⟨rfl, h₂⟩ := tag_eq h
  obtain ⟨rfl, hlen⟩ := UN.prefixFree 32 hl hl' h₂
  obtain ⟨rfl, -⟩ := List.append_inj (List.append_cancel_left h₂) hlen
  exact ⟨rfl, rfl⟩

theorem RawSec.functional : Functional (Seq RawSec) :=
  Seq.functional RawSec.prefixFree fun _ ⟨_, _, h⟩ => List.cons_ne_nil _ _ h.symm

theorem seq_append {G : Bytes → α → Prop} {b₁ b₂ : Bytes} {l₁ l₂ : List α}
    (h₁ : Seq G b₁ l₁) (h₂ : Seq G b₂ l₂) : Seq G (b₁ ++ b₂) (l₁ ++ l₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons hb _ ih =>
    rw [List.append_assoc, List.cons_append]
    exact .cons hb ih

/-- Custom sections are raw sections with id `0`. -/
theorem Customs.raw {c : Bytes} (h : Customs c) :
    ∃ l, Seq RawSec c l ∧ ∀ p ∈ l, p.1 = 0 := by
  induction h with
  | nil => exact ⟨[], .nil, fun _ hp => nomatch hp⟩
  | cons hc _ ih =>
    obtain ⟨_, hs⟩ := hc
    obtain ⟨l, hl, hl0⟩ := ih
    cases hs with
    | @mk lb c len _ hlb hlen _ =>
      refine ⟨(0, c) :: l, .cons ⟨lb, hlen ▸ hlb, rfl⟩ hl, fun p hp => ?_⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · rfl
      · exact hl0 p hp
    | empty => exact ⟨l, hl, hl0⟩

theorem filter_customs {l : List (UInt8 × Bytes)} (h : ∀ p ∈ l, p.1 = 0) {M : UInt8}
    (hM : M ≠ 0) : l.filter (fun p => p.1 == M) = [] := by
  rw [List.filter_eq_nil_iff]
  intro p hp
  rw [h p hp, beq_iff_eq]
  exact fun e => hM e.symm

/-- The raw view of an optional section: absent, or one raw section with id `N`
whose contents parse. -/
def SecView (N : UInt8) (G : Bytes → List α → Prop) (l : List (UInt8 × Bytes))
    (xs : List α) : Prop :=
  (l = [] ∧ xs = []) ∨ ∃ c, l = [(N, c)] ∧ G c xs

theorem Section.raw {N : UInt8} {G : Bytes → List α → Prop} {b : Bytes} {xs : List α}
    (h : Section N G b xs) : ∃ l, Seq RawSec b l ∧ SecView N G l xs := by
  cases h with
  | @mk lb c len _ hl hlen hc =>
    have hs := Seq.cons (G := RawSec) (a := (N, c)) ⟨lb, hlen ▸ hl, rfl⟩ Seq.nil
    rw [List.append_nil] at hs
    exact ⟨_, hs, .inr ⟨c, rfl, hc⟩⟩
  | empty => exact ⟨[], .nil, .inl ⟨rfl, rfl⟩⟩

theorem SecView.filter {N : UInt8} {G : Bytes → List α → Prop} {l : List (UInt8 × Bytes)}
    {xs : List α} (h : SecView N G l xs) (M : UInt8) :
    l.filter (fun p => p.1 == M) = if N = M then l else [] := by
  rcases h with ⟨rfl, -⟩ | ⟨c, rfl, -⟩
  · split <;> rfl
  · by_cases hNM : N = M
    · subst hNM
      simp
    · simp [hNM]

theorem SecView.functional {N : UInt8} {G : Bytes → List α → Prop} (hG : Functional G)
    {l : List (UInt8 × Bytes)} {xs xs' : List α} (h : SecView N G l xs)
    (h' : SecView N G l xs') : xs = xs' := by
  rcases h with ⟨rfl, rfl⟩ | ⟨c, rfl, hc⟩ <;> rcases h' with ⟨he, rfl⟩ | ⟨c', he, hc'⟩
  · rfl
  · exact absurd he (List.cons_ne_nil _ _).symm
  · exact absurd he (List.cons_ne_nil _ _)
  · simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at he
    subst he
    exact hG hc hc'

end Raw

/-- A map of expressions that agrees with the expression grammars lifts to modules. -/
theorem Module.map {E' : Type} {G : Bytes → E → Prop} {G' : Bytes → E' → Prop} (f : E → E')
    (hf : ∀ {b e}, G b e → G' b (f e)) {b : Bytes} {m : Scalar.Module E} (hm : Module G b m) :
    Module G' b
      { m with
        funcs := m.funcs.map (Declaration.Func.mapBody f)
        globals := m.globals.map (Declaration.Global.mapInit f)
        elems := m.elems.map fun e => ⟨e.table, f e.offset, e.init⟩
        data := m.data.map fun d => ⟨d.memory, f d.offset, d.bytes⟩ } := by
  cases hm with
  | mk h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅ hgl h₆ hex h₇ hst h₈ hel h₉ hco h₁₀ hda h₁₁
      hfuncs =>
    have h := Module.mk h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅
      (section_map _ (fun h => vec_map _ (fun h => Global.map f (fun h => hf h) h) h) hgl) h₆ hex h₇ hst h₈
      (section_map _ (fun h => vec_map _ (fun h => Elem.map f (fun h => hf h) h) h) hel) h₉
      (section_map _ (fun h => vec_map _ (fun h => Code.map f (fun h => hf h) h) h) hco) h₁₀
      (section_map _ (fun h => vec_map _ (fun h => Data.map f (fun h => hf h) h) h) hda) h₁₁
      (hfuncs.trans (List.length_map _).symm)
    rw [← zipFuncs_map] at h
    exact h

theorem Module.functional {G : Bytes → E → Prop} (hG : PrefixFree G) : Functional (Module G) := by
  intro b m m' hm hm'
  generalize hb : b = b' at hm'
  cases hm with
  | mk h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅ hgl h₆ hex h₇ hst h₈ hel h₉ hco h₁₀ hda h₁₁ _ =>
  cases hm' with
  | mk k₀ kty k₁ kim k₂ kfn k₃ ktb k₄ kme k₅ kgl k₆ kex k₇ kst k₈ kel k₉ kco k₁₀ kda k₁₁ _ =>
  cases hst with
  | mk hst =>
  cases kst with
  | mk kst =>
  simp only [List.append_assoc] at hb
  have hb := List.append_cancel_left (List.append_cancel_left hb)
  obtain ⟨_, s₀, v₀⟩ := Customs.raw h₀
  obtain ⟨_, s₁, v₁⟩ := Customs.raw h₁
  obtain ⟨_, s₂, v₂⟩ := Customs.raw h₂
  obtain ⟨_, s₃, v₃⟩ := Customs.raw h₃
  obtain ⟨_, s₄, v₄⟩ := Customs.raw h₄
  obtain ⟨_, s₅, v₅⟩ := Customs.raw h₅
  obtain ⟨_, s₆, v₆⟩ := Customs.raw h₆
  obtain ⟨_, s₇, v₇⟩ := Customs.raw h₇
  obtain ⟨_, s₈, v₈⟩ := Customs.raw h₈
  obtain ⟨_, s₉, v₉⟩ := Customs.raw h₉
  obtain ⟨_, s₁₀, v₁₀⟩ := Customs.raw h₁₀
  obtain ⟨_, s₁₁, v₁₁⟩ := Customs.raw h₁₁
  obtain ⟨_, sty, vty⟩ := Section.raw hty
  obtain ⟨_, sim, vim⟩ := Section.raw him
  obtain ⟨_, sfn, vfn⟩ := Section.raw hfn
  obtain ⟨_, stb, vtb⟩ := Section.raw htb
  obtain ⟨_, sme, vme⟩ := Section.raw hme
  obtain ⟨_, sgl, vgl⟩ := Section.raw hgl
  obtain ⟨_, sex, vex⟩ := Section.raw hex
  obtain ⟨_, sst, vst⟩ := Section.raw hst
  obtain ⟨_, sel, vel⟩ := Section.raw hel
  obtain ⟨_, sco, vco⟩ := Section.raw hco
  obtain ⟨_, sda, vda⟩ := Section.raw hda
  obtain ⟨_, t₀, w₀⟩ := Customs.raw k₀
  obtain ⟨_, t₁, w₁⟩ := Customs.raw k₁
  obtain ⟨_, t₂, w₂⟩ := Customs.raw k₂
  obtain ⟨_, t₃, w₃⟩ := Customs.raw k₃
  obtain ⟨_, t₄, w₄⟩ := Customs.raw k₄
  obtain ⟨_, t₅, w₅⟩ := Customs.raw k₅
  obtain ⟨_, t₆, w₆⟩ := Customs.raw k₆
  obtain ⟨_, t₇, w₇⟩ := Customs.raw k₇
  obtain ⟨_, t₈, w₈⟩ := Customs.raw k₈
  obtain ⟨_, t₉, w₉⟩ := Customs.raw k₉
  obtain ⟨_, t₁₀, w₁₀⟩ := Customs.raw k₁₀
  obtain ⟨_, t₁₁, w₁₁⟩ := Customs.raw k₁₁
  obtain ⟨_, tty, wty⟩ := Section.raw kty
  obtain ⟨_, tim, wim⟩ := Section.raw kim
  obtain ⟨_, tfn, wfn⟩ := Section.raw kfn
  obtain ⟨_, ttb, wtb⟩ := Section.raw ktb
  obtain ⟨_, tme, wme⟩ := Section.raw kme
  obtain ⟨_, tgl, wgl⟩ := Section.raw kgl
  obtain ⟨_, tex, wex⟩ := Section.raw kex
  obtain ⟨_, tst, wst⟩ := Section.raw kst
  obtain ⟨_, tel, wel⟩ := Section.raw kel
  obtain ⟨_, tco, wco⟩ := Section.raw kco
  obtain ⟨_, tda, wda⟩ := Section.raw kda
  have hs := seq_append s₀ <| seq_append sty <| seq_append s₁ <| seq_append sim <|
    seq_append s₂ <| seq_append sfn <| seq_append s₃ <| seq_append stb <|
    seq_append s₄ <| seq_append sme <| seq_append s₅ <| seq_append sgl <|
    seq_append s₆ <| seq_append sex <| seq_append s₇ <| seq_append sst <|
    seq_append s₈ <| seq_append sel <| seq_append s₉ <| seq_append sco <|
    seq_append s₁₀ <| seq_append sda s₁₁
  have ht := seq_append t₀ <| seq_append tty <| seq_append t₁ <| seq_append tim <|
    seq_append t₂ <| seq_append tfn <| seq_append t₃ <| seq_append ttb <|
    seq_append t₄ <| seq_append tme <| seq_append t₅ <| seq_append tgl <|
    seq_append t₆ <| seq_append tex <| seq_append t₇ <| seq_append tst <|
    seq_append t₈ <| seq_append tel <| seq_append t₉ <| seq_append tco <|
    seq_append t₁₀ <| seq_append tda t₁₁
  rw [hb] at hs
  have hL := RawSec.functional hs ht
  -- The raw sections with id `M ≠ 0` are those of the one section with that id.
  have key (M : UInt8) (_ : M ≠ 0) := congrArg (List.filter fun p => p.1 == M) hL
  have e := And.intro (key 1 (by decide)) <| And.intro (key 2 (by decide)) <|
    And.intro (key 3 (by decide)) <| And.intro (key 4 (by decide)) <|
    And.intro (key 5 (by decide)) <| And.intro (key 6 (by decide)) <|
    And.intro (key 7 (by decide)) <| And.intro (key 8 (by decide)) <|
    And.intro (key 9 (by decide)) <| And.intro (key 10 (by decide)) (key 11 (by decide))
  simp [List.filter_append, filter_customs v₀, filter_customs v₁, filter_customs v₂,
    filter_customs v₃, filter_customs v₄, filter_customs v₅, filter_customs v₆,
    filter_customs v₇, filter_customs v₈, filter_customs v₉, filter_customs v₁₀,
    filter_customs v₁₁, filter_customs w₀, filter_customs w₁, filter_customs w₂,
    filter_customs w₃, filter_customs w₄, filter_customs w₅, filter_customs w₆,
    filter_customs w₇, filter_customs w₈, filter_customs w₉, filter_customs w₁₀,
    filter_customs w₁₁, vty.filter, vim.filter, vfn.filter, vtb.filter, vme.filter,
    vgl.filter, vex.filter, vst.filter, vel.filter, vco.filter, vda.filter, wty.filter,
    wim.filter, wfn.filter, wtb.filter, wme.filter, wgl.filter, wex.filter, wst.filter,
    wel.filter, wco.filter, wda.filter] at e
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := e
  have e₁ := vty.functional (Vec.prefixFree V1.Binary.FuncType.prefixFree).functional wty
  have e₂ := vim.functional (Vec.prefixFree Import.prefixFree).functional wim
  have e₃ := vfn.functional (Vec.prefixFree Index.prefixFree).functional wfn
  have e₄ := vtb.functional (Vec.prefixFree V1.Binary.TableType.prefixFree).functional wtb
  have e₅ := vme.functional (Vec.prefixFree memType_prefixFree).functional wme
  have e₆ := vgl.functional (Vec.prefixFree (Global.prefixFree hG)).functional wgl
  have e₇ := vex.functional (Vec.prefixFree Export.prefixFree).functional wex
  have e₈ := vst.functional Start.functional wst
  have e₉ := vel.functional (Vec.prefixFree (Elem.prefixFree hG)).functional wel
  have e₁₀ := vco.functional (Vec.prefixFree (Code.prefixFree hG)).functional wco
  have e₁₁ := vda.functional (Vec.prefixFree (Data.prefixFree hG)).functional wda
  subst e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁
  rfl

/-- The empty module, for any expression grammar. -/
theorem Module.empty (G : Bytes → E → Prop) : Module G (magic ++ version) {} := by
  have h := Module.mk (G := G) (types := []) (imports := []) (typeidxs := []) (tables := [])
    (mems := []) (globals := []) (exports := []) (elems := []) (codes := []) (data := [])
    (h₀ := .nil) (hty := .empty) (h₁ := .nil) (him := .empty) (h₂ := .nil) (hfn := .empty)
    (h₃ := .nil) (htb := .empty) (h₄ := .nil) (hme := .empty) (h₅ := .nil) (hgl := .empty)
    (h₆ := .nil) (hex := .empty) (h₇ := .nil) (hst := .mk .empty) (h₈ := .nil) (hel := .empty)
    (h₉ := .nil) (hco := .empty) (h₁₀ := .nil) (hda := .empty) (h₁₁ := .nil) (hfuncs := rfl)
  exact h

end Silmaril.Wasm.Scalar.Binary

namespace Silmaril.Wasm.V1.Binary

open Silmaril.Wasm.Binary

/-- The Wasm 1.0 module grammar (REC 5.5.15) with the 1.0 expression grammar. -/
abbrev Encodes : Bytes → V1.Module → Prop := Scalar.Binary.Module Expr

end Silmaril.Wasm.V1.Binary

namespace Silmaril.Wasm.V1

instance : Encoding Module := ⟨Binary.Encodes⟩

theorem Binary.functional : Encoding.Functional Module := fun _ _ _ h h' =>
  Scalar.Binary.Module.functional Binary.Expr.prefixFree h h'

end Silmaril.Wasm.V1
