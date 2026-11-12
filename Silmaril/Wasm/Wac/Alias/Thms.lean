module

public import Silmaril.Wasm.Wac.Alias.Defs
public import Silmaril.Wasm.Wac.ElabComplete.Thms
public import Silmaril.Wasm.Wac.ElabTyped.Thms

/-!
# WAC alias expansion: aliases are transparent, expansion is idempotent

* `substA_alias`: on a normal table, a reference to an alias and its definiens expand to
  the same type, so comparing expanded types (`sub` on `Kind.expand`) compares up to
  aliases, as wac's `resolve_value_type` does;
* `substA_idem`: expanding twice is expanding once (on a normal table);
* `expand_wit`: expansion keeps kinds WIT-shaped;
* `elabDocA_iff`, `elabDocA_typed`: elaboration against the expanded registry is
  specified by `ElabDoc` and yields fully explicit, well-typed graphs.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef Owner)

namespace Alias

theorem mem_of_lookup {Γ : Table} {x : String} {t : Silmaril.Wasm.Wit.Binary.Ty} (h : Γ.lookup x = some t) : (x, t) ∈ Γ := by
  induction Γ with
  | nil => cases h
  | cons p Γ ih =>
    obtain ⟨y, u⟩ := p
    by_cases e : x = y
    · subst e
      have hu : u = t := by simpa [List.lookup] using h
      rw [hu]; exact List.mem_cons_self ..
    · have h' : Γ.lookup x = some t := by simpa [List.lookup, beq_false_of_ne e] using h
      exact List.mem_cons_of_mem _ (ih h')

theorem normal_of_lookup {Γ : Table} (hN : Normal Γ) {x : String} {t : Silmaril.Wasm.Wit.Binary.Ty} (h : Γ.lookup x = some t) :
    substA Γ t = t :=
  hN (x, t) (mem_of_lookup h)

/-- **An alias and its definiens expand to the same type.** -/
theorem substA_alias {Γ : Table} (hN : Normal Γ) {x : String} {t : Silmaril.Wasm.Wit.Binary.Ty} (h : Γ.lookup x = some t) :
    substA Γ (.ref ⟨.local, x⟩) = substA Γ t := by
  have e1 : substA Γ (.ref ⟨.local, x⟩) = t := by simp [substA, h]
  rw [e1, normal_of_lookup hN h]

theorem substA_ref_local (Γ : Table) (y : String) :
    substA Γ (.ref ⟨.local, y⟩) = (Γ.lookup y).getD (.ref ⟨.local, y⟩) := by
  simp [substA]

/-- The resource an alias of a resource stands for is not an alias itself. -/
theorem resOf_local {Γ : Table} (hN : Normal Γ) (x y : String) (h : resOf Γ x = ⟨.local, y⟩) :
    resOf Γ y = ⟨.local, y⟩ := by
  cases hx : Γ.lookup x with
  | none =>
    have e : y = x := by simp [resOf, hx] at h; exact h.symm
    rw [e]; simp [resOf, hx]
  | some t =>
    show resOf Γ y = ⟨.local, y⟩
    have hn : substA Γ t = t := normal_of_lookup hN hx
    cases t with
    | ref r =>
      show resOf Γ y = ⟨.local, y⟩
      have er : r = ⟨.local, y⟩ := by simpa [resOf, hx] using h
      subst er
      have hy : (Γ.lookup y).getD (.ref ⟨.local, y⟩) = .ref ⟨.local, y⟩ := by
        rw [← substA_ref_local]; exact hn
      cases hl : Γ.lookup y with
      | none => simp [resOf, hl]
      | some u =>
        have hu : u = .ref ⟨.local, y⟩ := by simpa [hl] using hy
        simp [resOf, hl, hu]
    | own r =>
      have er : r = ⟨.local, y⟩ := by simpa [resOf, hx] using h
      subst er
      simpa [substA] using hn
    | _ =>
      have e : y = x := by simp [resOf, hx] at h; exact h.symm
      rw [e]; simp [resOf, hx]

theorem substA_own_resOf {Γ : Table} (hN : Normal Γ) (x : String) :
    substA Γ (.own (resOf Γ x)) = .own (resOf Γ x) := by
  generalize hr : resOf Γ x = r
  obtain ⟨o, y⟩ := r
  cases o with
  | «local» => simp [substA, resOf_local hN x y hr]
  | iface i => simp [substA]

theorem substA_borrow_resOf {Γ : Table} (hN : Normal Γ) (x : String) :
    substA Γ (.borrow (resOf Γ x)) = .borrow (resOf Γ x) := by
  generalize hr : resOf Γ x = r
  obtain ⟨o, y⟩ := r
  cases o with
  | «local» => simp [substA, resOf_local hN x y hr]
  | iface i => simp [substA]

mutual
/-- **Expansion is idempotent** on a normal table. -/
theorem substA_idem {Γ : Table} (hN : Normal Γ) : ∀ t : Silmaril.Wasm.Wit.Binary.Ty, substA Γ (substA Γ t) = substA Γ t
  | .prim _ => rfl
  | .ref ⟨.local, x⟩ => by
    cases hl : Γ.lookup x with
    | none => simp [substA, hl]
    | some t => simp [substA, hl, normal_of_lookup hN hl]
  | .ref ⟨.iface _, _⟩ => rfl
  | .list t => by simp only [substA, substA_idem hN t]
  | .fixedList t _ => by simp only [substA, substA_idem hN t]
  | .map k v => by simp only [substA, substA_idem hN k, substA_idem hN v]
  | .option t => by simp only [substA, substA_idem hN t]
  | .result a b => by simp only [substA, substAOpt_idem hN a, substAOpt_idem hN b]
  | .tuple ts => by simp only [substA, substAs_idem hN ts]
  | .own ⟨.local, x⟩ => by simp only [substA]; exact substA_own_resOf hN x
  | .own ⟨.iface _, _⟩ => rfl
  | .borrow ⟨.local, x⟩ => by simp only [substA]; exact substA_borrow_resOf hN x
  | .borrow ⟨.iface _, _⟩ => rfl
  | .future t => by simp only [substA, substAOpt_idem hN t]
  | .stream t => by simp only [substA, substAOpt_idem hN t]
theorem substAOpt_idem {Γ : Table} (hN : Normal Γ) : ∀ t : Option Silmaril.Wasm.Wit.Binary.Ty, substAOpt Γ (substAOpt Γ t) = substAOpt Γ t
  | none => rfl
  | some t => by simp only [substAOpt, substA_idem hN t]
theorem substAs_idem {Γ : Table} (hN : Normal Γ) : ∀ ts : List Silmaril.Wasm.Wit.Binary.Ty, substAs Γ (substAs Γ ts) = substAs Γ ts
  | [] => rfl
  | t :: ts => by simp only [substAs, substA_idem hN t, substAs_idem hN ts]
end

/-! ## WIT shape -/

theorem expandIn_flat (Γ : Table) : ∀ k : Kind, k.flat = true → (expandIn Γ k).flat = true
  | .func _, _ | .value _, _ | .resource _, _ => rfl
  | .type k, h => by
    simp only [expandIn, Kind.flat] at h ⊢
    exact expandIn_flat Γ k h
  | .inst _ _, h | .comp _ _ _, h => by simp [Kind.flat] at h

theorem mem_expandEx {Γ : Table} : ∀ {es : Externs} {p : String × Kind}, p ∈ expandEx Γ es →
    ∃ q ∈ es, p = (q.1, expandIn Γ q.2)
  | [], _, h => by simp [expandEx] at h
  | (n, k) :: rest, p, h => by
    rcases List.mem_cons.1 h with e | h'
    · exact ⟨(n, k), List.mem_cons_self .., e⟩
    · obtain ⟨q, hq, e⟩ := mem_expandEx h'
      exact ⟨q, List.mem_cons_of_mem _ hq, e⟩

theorem expandIn_wit (Γ : Table) (k : Kind) (h : k.wit = true) : (expandIn Γ k).wit = true := by
  cases k with
  | inst id es =>
    have hes : ∀ p ∈ es, p.2.flat = true := by simpa [Kind.wit] using h
    have goal : ∀ p ∈ expandEx (normTable (aliases es)) es, p.2.flat = true := fun p hp => by
      obtain ⟨q, hq, rfl⟩ := mem_expandEx hp
      exact expandIn_flat _ q.2 (hes q hq)
    simpa [expandIn, Kind.wit] using goal
  | comp => simp [Kind.wit, Kind.flat] at h
  | func | value | resource => rfl
  | type k => exact expandIn_flat Γ (.type k) h

end Alias

/-- **Expansion keeps kinds WIT-shaped.** -/
theorem expand_wit {k : Kind} (h : k.wit = true) : k.expand.wit = true := Alias.expandIn_wit [] k h

theorem witEx_expandEx {es : Externs} (h : Implicit.WitEx es) : Implicit.WitEx (Alias.expandEx [] es) :=
  fun p hp => by
    obtain ⟨q, hq, rfl⟩ := Alias.mem_expandEx hp
    exact Alias.expandIn_wit [] q.2 (h q hq)

theorem lookup_expand {env : PkgEnv} {key : String} {pk : PkgType} (h : (PkgEnv.expand env).lookup key = some pk) :
    ∃ pk0, env.lookup key = some pk0 ∧ pk = pk0.expand := by
  induction env with
  | nil => cases h
  | cons p env ih =>
    obtain ⟨k, v⟩ := p
    by_cases e : key = k
    · subst e
      have hv : v.expand = pk := by simpa [PkgEnv.expand, List.lookup] using h
      exact ⟨v, by simp [List.lookup], hv.symm⟩
    · have h' : (PkgEnv.expand env).lookup key = some pk := by
        simpa [PkgEnv.expand, List.lookup, beq_false_of_ne e] using h
      obtain ⟨pk0, h0, e0⟩ := ih h'
      exact ⟨pk0, by simpa [List.lookup, beq_false_of_ne e] using h0, e0⟩

theorem envWit_expand {env : PkgEnv} (hE : EnvWit env) : EnvWit env.expand := fun key pk h => by
  obtain ⟨pk0, h0, rfl⟩ := lookup_expand h
  exact witEx_expandEx (hE key pk0 h0)

/-- **Elaboration up to aliases is specified by `ElabDoc`** (on the expanded registry). -/
theorem elabDocA_iff {env : PkgEnv} {d : Syntax.Document} {g : CGraph} :
    elabDocA env d = .ok g ↔ ElabDoc env.expand d g := elabDoc_iff

/-- **Elaboration up to aliases yields fully explicit, well-typed graphs.** -/
theorem elabDocA_typed {env : PkgEnv} (hE : EnvWit env) {d : Syntax.Document} {g : CGraph}
    (h : elabDocA env d = .ok g) : g.Complete ∧ g.Typed :=
  elabDoc_typed (envWit_expand hE) h

end Silmaril.Wasm.Wac
