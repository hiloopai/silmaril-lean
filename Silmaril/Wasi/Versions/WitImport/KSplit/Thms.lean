module

public import Silmaril.Wasi.Versions.WitImport.KSplit.Defs

@[expose] public section

/-!
# The kernel importer, in steps: the composition theorems

Each theorem reassembles an evaluation of the importer from separately checked steps:

* `mapM_ok`: a `mapM` in `Except` succeeds with the pointwise results (`List.Forall₂`);
* `elabEnv_eq`: `Elab.elabEnv` from one `Elab.elabBody` equation per interface;
* `elabPackage_eq`: `Elab.elabPackage` from the bodies of the package's interfaces and the
  elaborated worlds;
* `elaborate_eq`: `Elab.elaborate` from the gated universe, `check`, the lookup of the package,
  the environment, the package and the two binary checks;
* `importKD_eq`: the importer from the parsed files and `elaborate`; `importK_of`,
  `kTable_of`, `kDrops_of` and `kRPkg_of` give the tables of `KImport` and the resolved package.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit

/-- A pointwise relation, mapped along a function of both sides. -/
theorem forall₂_zipWith {α β γ : Type} {R : α → β → Prop} {S : α → γ → Prop} {g : α → β → γ}
    (h : ∀ x y, R x y → S x (g x y)) :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → List.Forall₂ S xs (List.zipWith g xs ys)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hxy hs => .cons (h _ _ hxy) (forall₂_zipWith h hs)

/-- A pointwise relation, weakened. -/
theorem forall₂_imp {α β : Type} {R S : α → β → Prop} (h : ∀ x y, R x y → S x y) :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → List.Forall₂ S xs ys
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hxy hs => .cons (h _ _ hxy) (forall₂_imp h hs)

/-- A `mapM` in `Except` with pointwise successes succeeds. -/
theorem mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ (fun x y => f x = .ok y) xs ys → xs.mapM f = .ok ys
  | [], [], .nil => rfl
  | x :: xs, y :: ys, .cons h hs => by
    rw [List.mapM_cons, h, mapM_ok hs]
    rfl

/-- `Elab.elabEnv` from one body per interface. -/
theorem elabEnv_eq {c : Elab.Ctx} {xs : List (PackageName × Interface)} {bs : List Binary.Interface}
    (hx : envItems c.U = xs)
    (hb : List.Forall₂ (fun (x : PackageName × Interface) b =>
      Elab.elabBody c (.iface ⟨x.1, x.2.name⟩) x.2.items x.2.docs x.2.gates = some b) xs bs) :
    Elab.elabEnv c = .ok (envOfBodies xs bs) := by
  have h : Elab.elabEnv c = (envItems c.U).mapM (envStep c) := rfl
  rw [h, hx]
  apply mapM_ok
  refine forall₂_zipWith (fun x b hxb => ?_) hb
  simp only [envStep, hxb]
  rfl

/-- `Elab.elabPackage` from the bodies of its interfaces and its worlds. -/
theorem elabPackage_eq {c : Elab.Ctx} {env : Binary.Env} {P : Package} {Is : List Interface}
    {bs : List Binary.Interface} {Ws : List Silmaril.Wasm.Wit.World} {ws : List Binary.World}
    (hi : P.ifaces = Is) (hw : P.worlds = Ws)
    (hb : List.Forall₂ (fun (I : Interface) b =>
      Elab.elabBody c (.iface ⟨P.name, I.name⟩) I.items I.docs I.gates = some b) Is bs)
    (hW : List.Forall₂ (fun (W : Silmaril.Wasm.Wit.World) w =>
      Elab.elabWorld c env (c.U.worldIds.length + 1) ⟨P.name, W.name⟩ = .ok w) Ws ws) :
    Elab.elabPackage c env P = .ok ⟨Elab.pkgName P.name, P.docs.contents,
      List.zipWith (fun I b => (I.name, b)) Is bs, List.zipWith (fun W w => (W.name, w)) Ws ws⟩ := by
  unfold Elab.elabPackage
  rw [hi, hw]
  rw [mapM_ok (xs := Is) (ys := List.zipWith (fun I b => (I.name, b)) Is bs) ?h1]
  · rw [mapM_ok (xs := Ws) (ys := List.zipWith (fun W w => (W.name, w)) Ws ws) ?h2]
    · rfl
    · refine forall₂_zipWith (fun W w hWw => ?_) hW
      simp only [hWw]
      rfl
  · refine forall₂_zipWith (fun I b hIb => ?_) hb
    simp only [hIb]
    rfl

/-- `Elab.elaborate` (no features) from its steps. -/
theorem elaborate_eq {U U' : Universe} {p : PackageName} {P : Package} {env : Binary.Env}
    {out : Binary.Package}
    (hg : Universe.gate [] U = U') (hc : check U' = true) (hP : Elab.lookupPkg U' p = .ok P)
    (he : Elab.elabEnv (Elab.Ctx.ofUniverse U') = .ok env)
    (hp : Elab.elabPackage (Elab.Ctx.ofUniverse U') env P = .ok out)
    (hv : Elab.Package.validB out (depsOf env p) = true)
    (hu : Elab.Package.namesUniqueB out = true) :
    Elab.elaborate U p [] = .ok (out, depsOf env p) := by
  unfold Elab.elaborate
  simp only [depsOf] at hv ⊢
  simp only [hg, hc, Elab.require, ite_true, hP, he, hp, hv, hu, pure, Except.pure, Bind.bind,
    Except.bind]

/-- The kernel importer from the parsed files and the elaboration. -/
theorem importKD_eq {sel : Bool} {srcs : List (List Char)} {ds : List Document} {p : PackageName}
    {r : Binary.Package × Binary.Env}
    (hd : List.Forall₂ (fun cs d => parseCharsK cs = some d) srcs ds)
    (hh : (kUniv sel ds).head?.map Package.name = some p)
    (he : Elab.elaborate (kUniv sel ds) p [] = .ok r) :
    importKD sel srcs = .ok r := by
  have h1 : srcs.mapM parseStep = .ok ds := by
    apply mapM_ok
    refine forall₂_imp (fun cs d hcd => ?_) hd
    simp only [parseStep, hcd]
  unfold importKD
  rw [h1]
  cases hU : (kUniv sel ds).head? with
  | none => rw [hU] at hh; cases hh
  | some P =>
    rw [hU] at hh
    simp only [Option.map_some, Option.some.injEq] at hh
    subst hh
    simp only [Bind.bind, Except.bind, Option.elim, pure, Except.pure, hU]
    exact he

/-- `importK` is the package of `importKD`. -/
theorem importK_eq (sel : Bool) (srcs : List (List Char)) :
    importK sel srcs = (importKD sel srcs).map Prod.fst := by
  have h : importK sel srcs = (do
      let ds ← srcs.mapM parseStep
      let U := kUniv sel ds
      let P ← U.head?.elim (.error "no package") pure
      let (B, _) ← Elab.elaborate U P.name []
      pure B) := rfl
  rw [h]
  unfold importKD
  cases srcs.mapM parseStep with
  | error e => rfl
  | ok ds =>
    simp only [Bind.bind, Except.bind]
    cases (kUniv sel ds).head? with
    | none => rfl
    | some P =>
      simp only [Option.elim, pure, Except.pure]
      cases Elab.elaborate _ P.name [] <;> rfl

/-- `importK` from `importKD`. -/
theorem importK_of {sel : Bool} {srcs : List (List Char)} {B : Binary.Package} {deps : Binary.Env}
    (h : importKD sel srcs = .ok (B, deps)) : importK sel srcs = .ok B := by
  rw [importK_eq, h]
  rfl

/-- The signature table of the kernel importer. -/
theorem kTable_of {ver sel : Bool} {srcs : List (List Char)} {B : Binary.Package} {deps : Binary.Env}
    (h : importKD sel srcs = .ok (B, deps)) : kTable ver sel srcs = some (table ver B) := by
  unfold kTable
  rw [importK_of h]

/-- The resource drops of the kernel importer. -/
theorem kDrops_of {ver : Bool} {srcs : List (List Char)} {B : Binary.Package} {deps : Binary.Env}
    (h : importKD false srcs = .ok (B, deps)) : kDrops ver srcs = some (drops ver B) := by
  unfold kDrops
  rw [importK_of h]

/-- The resolved package of the kernel importer. -/
theorem kRPkg_of {ver sel : Bool} {srcs : List (List Char)} {B : Binary.Package} {deps : Binary.Env}
    (h : importKD sel srcs = .ok (B, deps)) : kRPkg ver sel srcs = some (rtable ver B, envOf B deps) := by
  unfold kRPkg
  rw [h]

end Silmaril.Wasi.Versions.WitImport
