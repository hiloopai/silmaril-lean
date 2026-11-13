module

public import Silmaril.Wasm.Resource.ExternClientExamples.Defs
public import Silmaril.Wasm.Resource.ExternClient.Thms

/-!
# Runs of the `externref` clients that allocate, then call two imports

Both modules of `Silmaril.Wasm.Resource.ExternClientExamples` export `run` (address `3`) with body
`call $alloc; local.set 0; local.get 0; call $b₁; local.get 0; call $b₂`. `RunShape S b₁ b₂ …`
records the instantiated store `S` (`shapeB`, decided by kernel evaluation for each module).
Hand-built host-free Core runs, valid at every profile:

* `firstPlay_mem`: the export call reaches the callout `alloc`; the answer `values (pre ++ [h])`
  (in the same store) resumes it; the run reaches the callout `b₁ h`.
* `secondPlay_mem`: the answer `values []` to `b₁ h` resumes it; the run reaches the callout
  `b₂ h`.

New proofs, following `Silmaril.Proofs.Wasm.Resource.ExternExamples.Basic`.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.ExternClientExamples

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.UntypedExample Silmaril.Wasm.Resource
  Silmaril.Wasm.Resource.ExternExamples Silmaril.Wasm.Resource.ExternClient
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (decompose_fill)

/-- `[] → []`. -/
abbrev voidTy : CCompType := .func (Ty.ofList []) (Ty.ofList [])

/-- The shape of the body of `run`, with the imports it calls second and third. -/
def bodyB (b₁ b₂ : Nat) : FuncCode Nat → Bool
  | .wasm ⟨_, ls, [.call y₀, .localSet x₁, .localGet x₂, .call y₁, .localGet x₃, .call y₂]⟩ =>
    ls.length == 1 && y₀.toNat == 0 && x₁.toNat == 0 && x₂.toNat == 0 && y₁.toNat == b₁ &&
      x₃.toNat == 0 && y₂.toNat == b₂
  | _ => false

/-- **The shape of an instantiated store**, as a Boolean check. -/
def shapeB (S : Store Nat) (b₁ b₂ : Nat) : Bool :=
  match S.funcs[0]?, S.funcs[b₁]?, S.funcs[b₂]?, S.funcs[3]? with
  | some f0, some g1, some g2, some fr =>
    hostCode? f0 == some 0 && hostCode? g1 == some b₁ && hostCode? g2 == some b₂ &&
      f0.type.expand? == some allocTy && g1.type.expand? == some useTy &&
      g2.type.expand? == some useTy && fr.type.expand? == some voidTy &&
      fr.module.funcs == [0, 1, 2, 3] && ([0, 1, 2, 3][b₁]? == some b₁) &&
      ([0, 1, 2, 3][b₂]? == some b₂) && bodyB b₁ b₂ fr.code
  | _, _, _, _ => false

/-- The shape of an instantiated store. -/
structure RunShape (S : Store Nat) (b₁ b₂ : Nat) (f0 g1 g2 fr : FuncInst Nat) (t : TypeIdx)
    (ls : List ValType) (y₀ y₁ y₂ : FuncIdx) (x₁ x₂ x₃ : LocalIdx) : Prop where
  get0 : S.funcs[0]? = some f0
  get1 : S.funcs[b₁]? = some g1
  get2 : S.funcs[b₂]? = some g2
  get3 : S.funcs[3]? = some fr
  code0 : f0.code = .host 0
  code1 : g1.code = .host b₁
  code2 : g2.code = .host b₂
  ty0 : Expand f0.type allocTy
  ty1 : Expand g1.type useTy
  ty2 : Expand g2.type useTy
  tyR : Expand fr.type voidTy
  modR : fr.module.funcs = [0, 1, 2, 3]
  fb₁ : [0, 1, 2, 3][b₁]? = some b₁
  fb₂ : [0, 1, 2, 3][b₂]? = some b₂
  codeR : fr.code = .wasm ⟨t, ls,
    [.call y₀, .localSet x₁, .localGet x₂, .call y₁, .localGet x₃, .call y₂]⟩
  hls : ls.length = 1
  hy₀ : y₀.toNat = 0
  hx₁ : x₁.toNat = 0
  hx₂ : x₂.toNat = 0
  hy₁ : y₁.toNat = b₁
  hx₃ : x₃.toNat = 0
  hy₂ : y₂.toNat = b₂

theorem bodyB_code {b₁ b₂ : Nat} {c : FuncCode Nat} (h : bodyB b₁ b₂ c = true) :
    ∃ t ls y₀ y₁ y₂ x₁ x₂ x₃, c = .wasm ⟨t, ls,
        [.call y₀, .localSet x₁, .localGet x₂, .call y₁, .localGet x₃, .call y₂]⟩ ∧
      ls.length = 1 ∧ y₀.toNat = 0 ∧ x₁.toNat = 0 ∧ x₂.toNat = 0 ∧ y₁.toNat = b₁ ∧
      x₃.toNat = 0 ∧ y₂.toNat = b₂ := by
  unfold bodyB at h
  split at h
  · rename_i t ls y₀ x₁ x₂ y₁ x₃ y₂
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩ := h
    exact ⟨t, ls, y₀, y₁, y₂, x₁, x₂, x₃, rfl, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  · cases h

theorem shapeB_sound {S : Store Nat} {b₁ b₂ : Nat} (h : shapeB S b₁ b₂ = true) :
    ∃ f0 g1 g2 fr t ls y₀ y₁ y₂ x₁ x₂ x₃, RunShape S b₁ b₂ f0 g1 g2 fr t ls y₀ y₁ y₂ x₁ x₂ x₃ := by
  unfold shapeB at h
  split at h
  · rename_i f0 g1 g2 fr h0 h1 h2 h3
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, e0⟩, e1⟩, e2⟩, eR⟩, hm⟩, m1⟩, m2⟩, hb⟩ := h
    obtain ⟨t, ls, y₀, y₁, y₂, x₁, x₂, x₃, hc, hls, hy₀, hx₁, hx₂, hy₁, hx₃, hy₂⟩ := bodyB_code hb
    exact ⟨f0, g1, g2, fr, t, ls, y₀, y₁, y₂, x₁, x₂, x₃, h0, h1, h2, h3, hostCode?_code c0,
      hostCode?_code c1, hostCode?_code c2, Expand.iff.2 e0, Expand.iff.2 e1, Expand.iff.2 e2,
      Expand.iff.2 eR, hm, m1, m2, hc, hls, hy₀, hx₁, hx₂, hy₁, hx₃, hy₂⟩
  · cases h

/-! ## Steps inside the body of `run` -/

/-- The code of `run` with its frame. -/
abbrev bodyC (F : Frame) (code : List Admin) : List Admin := [.frame 0 F [.label 0 [] code]]

theorem inBody {P : Profile} {s s' : Store Nat} {F F' : Frame} {is is' : List Admin}
    (h : Step P (fun _ _ _ _ => False) ⟨s, F, is⟩ ⟨s', F', is'⟩) (pre : List Val)
    (rest : List Admin) :
    InternalP P (s, .active {} (bodyC F (vals pre ++ is ++ rest)))
      (s', .active {} (bodyC F' (vals pre ++ is' ++ rest))) := by
  have h₁ : Step P (fun _ _ _ _ => False) ⟨s, F, vals pre ++ is ++ rest⟩
      ⟨s', F', vals pre ++ is' ++ rest⟩ := by
    by_cases hp : pre = [] ∧ rest = []
    · obtain ⟨rfl, rfl⟩ := hp
      simpa [vals] using h
    · exact Step.ctxtInstrs h (by simpa only [ne_eq, not_and_or] using hp)
  exact ⟨_, _, rfl, Step.ctxtFrame (Step.ctxtLabel h₁)⟩

/-- The context of a callout inside the body of `run`. -/
abbrev ctxB (F : Frame) (pre : List Val) (rest : List Admin) : Ctx :=
  .frame [] 0 F (.label [] 0 [] (.top pre rest) []) []

theorem ctxB_fill (F : Frame) (pre : List Val) (rest Y : List Admin) :
    (ctxB F pre rest).fill Y = bodyC F (vals pre ++ Y ++ rest) := by
  simp [Ctx.fill, vals]

theorem callout_body {S : Store Nat} {F : Frame} {pre args : List Val} {rest : List Admin} {a : Nat}
    {fi : FuncInst Nat} {h : Nat} {ps rs : Ty (.list .val)} {d : DefType}
    (hf : S.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hcode : fi.code = .host h)
    (hn : args.length = ps.length) :
    decompose? S (bodyC F (vals pre ++ (vals args ++ [.ref (.func a), .callRefType d]) ++ rest)) =
      some (ctxB F pre rest, a, h, args) := by
  rw [← ctxB_fill]
  exact decompose_fill hf he hcode (c := .callRefType d) trivial hn _

theorem resume_body {S : Store Nat} {F : Frame} {X : List Admin} {E : Ctx} {a h : Nat}
    {args : List Val} (hd : decompose? S (bodyC F X) = some (E, a, h, args)) (r : Result) :
    resumeResult S (.active {} (bodyC F X)) r = .active {} (E.fill r.toAdmin) := by
  simp only [resumeResult, Thread.config, hd]

theorem inBody' {P : Profile} {s s' : Store Nat} {F F' : Frame} {is is' : List Admin}
    (h : Step P (fun _ _ _ _ => False) ⟨s, F, is⟩ ⟨s', F', is'⟩) (pre : List Val)
    (rest : List Admin) {A B : List Admin} (hA : A = vals pre ++ is ++ rest)
    (hB : B = vals pre ++ is' ++ rest) :
    InternalP P (s, .active {} (bodyC F A)) (s', .active {} (bodyC F' B)) := by
  subst hA hB; exact inBody h pre rest

/-! ## The plays -/

section Plays
variable {P : Profile} {S : Store Nat} {b₁ b₂ : Nat} {f0 g1 g2 fr : FuncInst Nat} {t : TypeIdx}
  {ls : List ValType} {y₀ y₁ y₂ : FuncIdx} {x₁ x₂ x₃ : LocalIdx}

/-- The frame of `run`. -/
abbrev frameA (fr : FuncInst Nat) (ls : List ValType) : Frame := Frame.forCall fr.module [] ls

/-- The rest of the body after `call $alloc`. -/
abbrev rest5 (x₁ x₂ x₃ : LocalIdx) (y₁ y₂ : FuncIdx) : List Admin :=
  [.plain (.localSet x₁), .plain (.localGet x₂), .plain (.call y₁), .plain (.localGet x₃),
    .plain (.call y₂)]

/-- The rest of the body after `call $b₁`. -/
abbrev rest2 (x₃ : LocalIdx) (y₂ : FuncIdx) : List Admin :=
  [.plain (.localGet x₃), .plain (.call y₂)]

/-- The code at the callout `alloc`. -/
abbrev codeA (f0 fr : FuncInst Nat) (ls : List ValType) (x₁ x₂ x₃ : LocalIdx) (y₁ y₂ : FuncIdx) :
    List Admin :=
  bodyC (frameA fr ls) (vals [] ++ (vals [] ++ [.ref (.func 0), .callRefType f0.type]) ++
    rest5 x₁ x₂ x₃ y₁ y₂)

/-- The code at the callout `b₁ h`. -/
abbrev codeB (b₁ : Nat) (g1 : FuncInst Nat) (F : Frame) (pre : List Val) (h : Val)
    (x₃ : LocalIdx) (y₂ : FuncIdx) : List Admin :=
  bodyC F (vals pre ++ (vals [h] ++ [.ref (.func b₁), .callRefType g1.type]) ++ rest2 x₃ y₂)

/-- The code at the callout `b₂ h`. -/
abbrev codeC (b₂ : Nat) (g2 : FuncInst Nat) (F : Frame) (h : Val) : List Admin :=
  bodyC F (vals [] ++ (vals [h] ++ [.ref (.func b₂), .callRefType g2.type]) ++ [])

theorem reach_alloc (hs : RunShape S b₁ b₂ f0 g1 g2 fr t ls y₀ y₁ y₂ x₁ x₂ x₃) :
    Reach P (S, .pending 3 []) (S, .active {} (codeA f0 fr ls x₁ x₂ x₃ y₁ y₂)) := by
  have i₁ : InternalP P (S, Thread.pending 3 [])
      (S, .active {} (bodyC (frameA fr ls) (vals [] ++ [.plain (.call y₀)] ++
        rest5 x₁ x₂ x₃ y₁ y₂))) :=
    ⟨_, _, rfl, Step.callRefFunc (s := S) (f := {})
      (c := .callRefType ((S.funcs[3]?.map FuncInst.type).getD default)) (vs := [])
      trivial hs.get3 hs.tyR rfl hs.codeR⟩
  have hx : (frameA fr ls).module.funcs[y₀.toNat]? = some 0 := by
    simp [Frame.forCall, hs.modR, hs.hy₀]
  have i₂ := inBody (P := P) (Step.call hx hs.get0) [] (rest5 x₁ x₂ x₃ y₁ y₂)
  exact (Relation.ReflTransGen.single i₁).tail i₂

theorem reach_b₁ (hs : RunShape S b₁ b₂ f0 g1 g2 fr t ls y₀ y₁ y₂ x₁ x₂ x₃) (pre : List Val)
    (h : Val) :
    Reach P (S, .active {} (bodyC (frameA fr ls) (vals [] ++ vals (pre ++ [h]) ++
        rest5 x₁ x₂ x₃ y₁ y₂)))
      (S, .active {} (codeB b₁ g1 ((frameA fr ls).setLocal x₁ h) pre h x₃ y₂)) := by
  have hlen : x₁.toNat < (frameA fr ls).locals.length := by
    simp [Frame.forCall, hs.hls, hs.hx₁]
  have hl : ((frameA fr ls).setLocal x₁ h).local? x₂ = some (some h) := by
    obtain ⟨l, hl⟩ := List.length_eq_one_iff.1 hs.hls
    simp [Frame.local?, Frame.setLocal, Frame.forCall, hl, hs.hx₁, hs.hx₂]
  have hx : ((frameA fr ls).setLocal x₁ h).module.funcs[y₁.toNat]? = some b₁ := by
    simp [Frame.setLocal, Frame.forCall, hs.modR, hs.hy₁, hs.fb₁]
  have i₁ := inBody' (P := P) (s := S) (Step.«variable» (VariableStep.localSet (v := h) hlen)) pre
    [.plain (.localGet x₂), .plain (.call y₁), .plain (.localGet x₃), .plain (.call y₂)]
    (A := vals [] ++ vals (pre ++ [h]) ++ rest5 x₁ x₂ x₃ y₁ y₂) (by simp [vals]) rfl
  have i₂ := inBody' (P := P) (s := S) (Step.«variable» (VariableStep.localGet hl)) pre
    [.plain (.call y₁), .plain (.localGet x₃), .plain (.call y₂)]
    (A := vals pre ++ [] ++ [.plain (.localGet x₂), .plain (.call y₁), .plain (.localGet x₃),
      .plain (.call y₂)]) (by simp) rfl
  have i₃ := inBody' (P := P) (s := S) (Step.call hx hs.get1) (pre ++ [h]) (rest2 x₃ y₂)
    (A := vals pre ++ [h.toAdmin] ++ [.plain (.call y₁), .plain (.localGet x₃), .plain (.call y₂)])
    (by simp [vals]) (B := vals pre ++ (vals [h] ++ [.ref (.func b₁), .callRefType g1.type]) ++
      rest2 x₃ y₂) (by simp [vals])
  exact ((Relation.ReflTransGen.single i₁).tail i₂).tail i₃

theorem reach_b₂ (hs : RunShape S b₁ b₂ f0 g1 g2 fr t ls y₀ y₁ y₂ x₁ x₂ x₃) (h : Val) :
    Reach P (S, .active {} (bodyC ((frameA fr ls).setLocal x₁ h) (vals [] ++ vals [] ++
        rest2 x₃ y₂)))
      (S, .active {} (codeC b₂ g2 ((frameA fr ls).setLocal x₁ h) h)) := by
  have hl : ((frameA fr ls).setLocal x₁ h).local? x₃ = some (some h) := by
    obtain ⟨l, hl⟩ := List.length_eq_one_iff.1 hs.hls
    simp [Frame.local?, Frame.setLocal, Frame.forCall, hl, hs.hx₁, hs.hx₃]
  have hx : ((frameA fr ls).setLocal x₁ h).module.funcs[y₂.toNat]? = some b₂ := by
    simp [Frame.setLocal, Frame.forCall, hs.modR, hs.hy₂, hs.fb₂]
  have i₁ := inBody' (P := P) (s := S) (Step.«variable» (VariableStep.localGet hl)) []
    [.plain (.call y₂)] (A := vals [] ++ vals [] ++ rest2 x₃ y₂) (by simp [vals]) rfl
  have i₂ := inBody' (P := P) (s := S) (Step.call hx hs.get2) [h] []
    (A := vals [] ++ [h.toAdmin] ++ [.plain (.call y₂)]) (by simp [vals])
    (B := vals [] ++ (vals [h] ++ [.ref (.func b₂), .callRefType g2.type]) ++ []) (by simp [vals])
  exact (Relation.ReflTransGen.single i₁).tail i₂

theorem length_ofList_nil : (Ty.ofList ([] : List CValType)).length = 0 := by
  rw [Ty.length_ofList]; rfl

theorem length_ofList_one : (Ty.ofList [externC]).length = 1 := by
  rw [Ty.length_ofList]; rfl

/-- **The export call reaches `alloc`; the answer `values (pre ++ [h])` leads to the callout
`b₁ h`** (every profile). -/
theorem run₁ (hs : RunShape S b₁ b₂ f0 g1 g2 fr t ls y₀ y₁ y₂ x₁ x₂ x₃) {U : UInstance}
    (f : U.F.Op) (pre : List Val) (h : Val) :
    (U.lts P).Run (.running f S (.pending 3 []))
      [.inl (.ask ⟨0, S, []⟩), .inl (.ans ⟨0, S, []⟩ ⟨S, .values (pre ++ [h])⟩),
        .inl (.ask ⟨b₁, S, [h]⟩)]
      (.waiting f S (.active {} (codeB b₁ g1 ((frameA fr ls).setLocal x₁ h) pre h x₃ y₂))
        ⟨b₁, S, [h]⟩) := by
  have hd₁ : decompose? S (codeA f0 fr ls x₁ x₂ x₃ y₁ y₂) =
      some (ctxB (frameA fr ls) [] (rest5 x₁ x₂ x₃ y₁ y₂), 0, 0, []) :=
    callout_body hs.get0 hs.ty0 hs.code0 length_ofList_nil.symm
  have hd₂ : decompose? S (codeB b₁ g1 ((frameA fr ls).setLocal x₁ h) pre h x₃ y₂) =
      some (ctxB ((frameA fr ls).setLocal x₁ h) pre (rest2 x₃ y₂), b₁, b₁, [h]) :=
    callout_body hs.get1 hs.ty1 hs.code1 length_ofList_one.symm
  have hres := resume_body hd₁ (.values (pre ++ [h]))
  rw [ctxB_fill] at hres
  have r₂ : (U.lts P).Run (.running f S (resumeResult S (.active {} (codeA f0 fr ls x₁ x₂ x₃ y₁ y₂))
      (.values (pre ++ [h])))) [.inl (.ask ⟨b₁, S, [h]⟩)]
      (.waiting f S (.active {} (codeB b₁ g1 ((frameA fr ls).setLocal x₁ h) pre h x₃ y₂))
        ⟨b₁, S, [h]⟩) := by
    rw [hres]
    exact (run_of_reach (U := U) f (reach_b₁ (P := P) hs pre h)).append
      (.vis (UInstance.Trans.ucall ⟨_, _, hd₂⟩) (.nil _))
  exact (run_of_reach (U := U) f (reach_alloc (P := P) hs)).append
    (.vis (UInstance.Trans.ucall ⟨_, _, hd₁⟩)
      (.vis (UInstance.Trans.uret (⟨S, .values (pre ++ [h])⟩ : UReply)) r₂))

/-- **The answer `values []` to `b₁ h` leads to the callout `b₂ h`** (every profile). -/
theorem run₂ (hs : RunShape S b₁ b₂ f0 g1 g2 fr t ls y₀ y₁ y₂ x₁ x₂ x₃) {U : UInstance}
    (f : U.F.Op) (h : Val) :
    (U.lts P).Run (.waiting f S (.active {} (codeB b₁ g1 ((frameA fr ls).setLocal x₁ h) [] h x₃ y₂))
        ⟨b₁, S, [h]⟩)
      [.inl (.ans ⟨b₁, S, [h]⟩ ⟨S, .values []⟩), .inl (.ask ⟨b₂, S, [h]⟩)]
      (.waiting f S (.active {} (codeC b₂ g2 ((frameA fr ls).setLocal x₁ h) h)) ⟨b₂, S, [h]⟩) := by
  have hd₂ : decompose? S (codeB b₁ g1 ((frameA fr ls).setLocal x₁ h) [] h x₃ y₂) =
      some (ctxB ((frameA fr ls).setLocal x₁ h) [] (rest2 x₃ y₂), b₁, b₁, [h]) :=
    callout_body hs.get1 hs.ty1 hs.code1 length_ofList_one.symm
  have hd₃ : decompose? S (codeC b₂ g2 ((frameA fr ls).setLocal x₁ h) h) =
      some (ctxB ((frameA fr ls).setLocal x₁ h) [] [], b₂, b₂, [h]) :=
    callout_body hs.get2 hs.ty2 hs.code2 length_ofList_one.symm
  have hres := resume_body hd₂ (.values [])
  rw [ctxB_fill] at hres
  have r₃ : (U.lts P).Run (.running f S (resumeResult S
      (.active {} (codeB b₁ g1 ((frameA fr ls).setLocal x₁ h) [] h x₃ y₂)) (.values [])))
      [.inl (.ask ⟨b₂, S, [h]⟩)]
      (.waiting f S (.active {} (codeC b₂ g2 ((frameA fr ls).setLocal x₁ h) h)) ⟨b₂, S, [h]⟩) := by
    rw [hres]
    exact (run_of_reach (U := U) f (reach_b₂ (P := P) hs h)).append
      (.vis (UInstance.Trans.ucall ⟨_, _, hd₃⟩) (.nil _))
  exact .vis (UInstance.Trans.uret (⟨S, .values []⟩ : UReply)) r₃

/-- The first play: `run`, `alloc`, its answer `values (pre ++ [h])`, the call `b₁ h`. -/
def play₁ {ι : Type} (x : ι) (S : Store Nat) (b₁ : Nat) (pre : List Val) (h : Val) :
    List (Move UImp (untypedSig ι)) :=
  [.inr (.ask ⟨x, S, []⟩), .inl (.ask ⟨0, S, []⟩), .inl (.ans ⟨0, S, []⟩ ⟨S, .values (pre ++ [h])⟩),
    .inl (.ask ⟨b₁, S, [h]⟩)]

/-- The second play: the first, the answer `values []` to `b₁ h`, the call `b₂ h`. -/
def play₂ {ι : Type} (x : ι) (S : Store Nat) (b₁ b₂ : Nat) (h : Val) :
    List (Move UImp (untypedSig ι)) :=
  play₁ x S b₁ [] h ++ [.inl (.ans ⟨b₁, S, [h]⟩ ⟨S, .values []⟩), .inl (.ask ⟨b₂, S, [h]⟩)]

theorem init_eq {U : UInstance} {x : U.X} (hx : U.addr x = 3) (S : Store Nat) :
    U.init ⟨x, S, []⟩ = .pending 3 [] := by
  simp [UInstance.init, hx]

/-- **The first play is a play of the instance** (every profile). -/
theorem play₁_mem (hs : RunShape S b₁ b₂ f0 g1 g2 fr t ls y₀ y₁ y₂ x₁ x₂ x₃) {U : UInstance}
    {x : U.X} (hx : U.addr x = 3) (pre : List Val) (h : Val) :
    play₁ x S b₁ pre h ∈ U.strategy P := by
  have r := run₁ (P := P) hs (U := U) ⟨x, S, []⟩ pre h
  rw [← init_eq hx S] at r
  exact UInstance.mem_strategy_iff.2 ⟨_, .vis (UInstance.Trans.call ⟨x, S, []⟩) r⟩

/-- **The second play is a play of the instance** (every profile). -/
theorem play₂_mem (hs : RunShape S b₁ b₂ f0 g1 g2 fr t ls y₀ y₁ y₂ x₁ x₂ x₃) {U : UInstance}
    {x : U.X} (hx : U.addr x = 3) (h : Val) :
    play₂ x S b₁ b₂ h ∈ U.strategy P := by
  have r := (run₁ (P := P) hs (U := U) ⟨x, S, []⟩ [] h).append (run₂ hs _ h)
  rw [← init_eq hx S] at r
  exact UInstance.mem_strategy_iff.2 ⟨_, .vis (UInstance.Trans.call ⟨x, S, []⟩) r⟩

end Plays

end Silmaril.Wasm.Resource.ExternClientExamples
