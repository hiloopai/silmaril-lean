module

public import Silmaril.Servers.Conn.Defs
public import Silmaril.Servers.Core.Thms

/-!
# Connections: theorems

PROVED (standard axioms), namespace `Silmaril.Servers`.

* **`Sen.sc_of_merge`**: a trace is sequentially consistent with respect to `S` when some
  sequential use, with the same events on every connection, has its history in `S` (the
  connections' requests merged into one sequential order);
* `Sen.sc_congr`: sequential consistency only looks at the connections one by one;
* **`counter_sc`**, **`counter_not_lin`**: `counterTrace` is sequentially consistent with
  respect to the counter but not linearizable: the connections can be swapped, real time
  cannot;
* `Sen.inOrder_of_perConn`: in-order responses are a per-connection property;
* `Model.perConn_mono`, `Model.perConn_sat`: an instance per connection preserves refinement
  and turns every sentence of the instance into its per-connection sentence;
* **`Model.perConn_pipe_inOrder`**, `Model.perConn_pipe_lin`: with a pipelining instance of a
  machine per connection, the responses of every connection come in request order, and every
  connection is linearizable on its own;
* **`Model.perConn_ofRel`**: for a stateless machine, an instance per connection refines the
  shared atomic-handler server (so it is linearizable, and sequentially consistent): without
  state, the instances are indistinguishable from one.
-/

@[expose] public section

namespace Silmaril.Servers

variable {A : Sig}

/-! ## Sequential consistency -/

theorem Sen.sc_of_merge {S : SeqSpec A} {t : Trace A} (h : List (ReqId × A.Req × A.Resp))
    (hn : (h.map (·.1)).Nodup) (hc : ∀ c, (Trace.seq h).onConn c = t.onConn c)
    (hS : S (h.map (·.2))) : Sen.sc S t :=
  ⟨Trace.seq h, hc, (Sen.lin_seq_iff h hn).2 hS⟩

theorem Sen.sc_congr {S : SeqSpec A} {t u : Trace A} (hc : ∀ c, t.onConn c = u.onConn c)
    (h : Sen.sc S t) : Sen.sc S u :=
  let ⟨t₂, h₂, hl⟩ := h; ⟨t₂, fun c => (h₂ c).trans (hc c), hl⟩

theorem counter_sc : Sen.sc (counterM.Hist 0) counterTrace := by
  refine Sen.sc_of_merge (A := counterSig) [(⟨1, 0⟩, (), (0 : Nat)), (⟨0, 0⟩, (), (1 : Nat))] (by decide) (fun c => ?_)
    ⟨2, .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil _))⟩
  by_cases h0 : c = 0
  · subst h0; simp [Trace.onConn, Trace.seq, counterTrace, Event.id]
  · by_cases h1 : c = 1
    · subst h1; simp [Trace.onConn, Trace.seq, counterTrace, Event.id]
    · simp [Trace.onConn, Trace.seq, counterTrace, Event.id, Ne.symm h0, Ne.symm h1]

theorem counter_not_lin : ¬ Sen.lin (counterM.Hist 0) counterTrace := by
  rw [counterTrace, Sen.lin_seq_iff _ (by decide)]
  rintro ⟨q, hr⟩
  cases hr with
  | cons h _ => exact absurd h.1 (by decide)

/-! ## In-order responses -/

theorem Sen.inOrder_of_perConn {t : Trace A} (h : Sen.perConn Sen.inOrder t) : Sen.inOrder t := by
  intro pre post j s ht i r hi hc hs
  have hsplit : t.onConn j.conn =
      Trace.onConn j.conn pre ++ Event.send j s :: Trace.onConn j.conn post := by
    subst ht
    simp only [Trace.onConn, List.filter_append, List.filter_cons, Event.id, beq_self_eq_true,
      if_true]
  have hi' : Event.recv i r ∈ Trace.onConn j.conn pre :=
    List.mem_filter.2 ⟨hi, by simp [Event.id, hc]⟩
  obtain ⟨s', hs'⟩ := h j.conn _ _ j s hsplit i r hi' hc hs
  exact ⟨s', (List.mem_filter.1 hs').1⟩

/-! ## An instance per connection -/

theorem Model.perConn_mono {N N' : Model A} (h : N ≤ N') : Model.perConn N ≤ Model.perConn N' :=
  fun _ ⟨hw, hc⟩ => ⟨hw, fun c => h _ (hc c)⟩

theorem Model.perConn_sat {N : Model A} {φ : Sen A} (h : N.Sat φ) :
    (Model.perConn N).Sat (Sen.perConn φ) :=
  fun _ ⟨_, hc⟩ c => h _ (hc c)

theorem Model.perConn_pipe_inOrder {σ : Type} (M : Machine A σ) (q₀ : σ) :
    (Model.perConn (M.pipeServer q₀)).Sat Sen.inOrder :=
  fun t ht => Sen.inOrder_of_perConn (Model.perConn_sat (M.pipeServer_sat_inOrder q₀) t ht)

theorem Model.perConn_pipe_lin {σ : Type} (M : Machine A σ) (q₀ : σ) :
    (Model.perConn (M.pipeServer q₀)).Sat (Sen.perConn (Sen.lin (M.Hist q₀))) :=
  Model.perConn_sat (M.pipeServer_sat_lin q₀)

theorem Model.perConn_ofRel (R : A.Req → A.Resp → Prop) :
    (Model.perConn ((Machine.ofRel R).server ())).Refines ((Machine.ofRel R).server ()) := by
  intro t ⟨hw, hc⟩
  refine (Machine.server_ofRel_tr_iff R t).2 ⟨hw, fun i r s hr hs => ?_⟩
  have h := ((Machine.server_ofRel_tr_iff R _).1 (hc i.conn)).2 i r s
  exact h (List.mem_filter.2 ⟨hr, by simp [Event.id]⟩) (List.mem_filter.2 ⟨hs, by simp [Event.id]⟩)

end Silmaril.Servers
