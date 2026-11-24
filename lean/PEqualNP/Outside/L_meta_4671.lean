import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4671

open PEqualNP.CircuitLowerBounds

def phi (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (k : ℕ) : ℕ :=
  if h : k < x1 then (x3 ⟨k, h⟩ : ℕ) else k - x1 + x2

def rn (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (phi x1 x2 x3)⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc (l : List Bool) (v : Bool) (k : ℕ) :
    (l ++ [v]).getD k false =
      if k < l.length then l.getD k false else if k = l.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    have : k - l.length ≠ 0 := by omega
    simp [this]

def Inv (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (w w' : List Bool) : Prop :=
  ∃ m, w.length = x1 + m ∧ w'.length = x2 + m ∧
    ∀ k, w'.getD (phi x1 x2 x3 k) false = w.getD k false

lemma inv_step (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (w w' : List Bool) (g : Gate)
    (h : Inv x1 x2 x3 w w') : Inv x1 x2 x3 (step w g) (step w' (rn x1 x2 x3 g)) := by
  obtain ⟨m, hw, hw', hk⟩ := h
  have hv : (rn x1 x2 x3 g).op.eval ((rn x1 x2 x3 g).inputs.map fun i => w'.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simp only [rn, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hk i
  refine ⟨m + 1, by simp [step, hw]; omega, by simp [step, hw']; omega, ?_⟩
  intro k
  unfold step
  rw [hv, getD_snoc, getD_snoc]
  have hp : phi x1 x2 x3 k < x2 ∨ phi x1 x2 x3 k = k - x1 + x2 ∧ x1 ≤ k := by
    unfold phi
    split_ifs with hk1
    · exact Or.inl (x3 ⟨k, hk1⟩).isLt
    · exact Or.inr ⟨rfl, by omega⟩
  have hlt : k < x1 → phi x1 x2 x3 k < x2 := by
    intro hk1; unfold phi; rw [dif_pos hk1]; exact (x3 ⟨k, hk1⟩).isLt
  by_cases hk1 : k < x1
  · have := hlt hk1
    rw [if_pos (by omega), if_pos (by omega)]
    exact hk k
  · have he : phi x1 x2 x3 k = k - x1 + x2 := by unfold phi; rw [dif_neg hk1]
    have hkk := hk k
    rw [he] at hkk ⊢
    by_cases h1 : k < w.length
    · rw [if_pos (by omega), if_pos h1]; exact hkk
    · rw [if_neg (by omega), if_neg h1]
      by_cases h2 : k = w.length
      · rw [if_pos (by omega), if_pos h2]
      · rw [if_neg (by omega), if_neg h2]

lemma inv_fold (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) :
    ∀ (gs : List Gate) (w w' : List Bool), Inv x1 x2 x3 w w' →
      Inv x1 x2 x3 (gs.foldl step w) ((gs.map (rn x1 x2 x3)).foldl step w')
  | [], _, _, h => h
  | g :: gs, w, w', h => by
    simp only [List.foldl_cons, List.map_cons]
    exact inv_fold x1 x2 x3 gs _ _ (inv_step x1 x2 x3 w w' g h)

lemma inv_base (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x11 : Fin x2 → Bool) :
    Inv x1 x2 x3 (List.ofFn (x11 ∘ x3)) (List.ofFn x11) := by
  refine ⟨0, by simp, by simp, ?_⟩
  intro k
  simp only [List.getD_eq_getElem?_getD]
  unfold phi
  split_ifs with hk
  · have h2 := (x3 ⟨k, hk⟩).isLt
    simp [hk, h2]
  · rw [List.getElem?_eq_none (by simp only [List.length_ofFn]; omega), List.getElem?_eq_none (by simp only [List.length_ofFn]; omega)]

lemma phi_lt (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (s k : ℕ) (hk : k < x1 + s) :
    phi x1 x2 x3 k < x2 + s := by
  unfold phi
  split_ifs with h
  · have := (x3 ⟨k, h⟩).isLt; omega
  · omega

end PEqualNP.Outside.L_meta_4671

theorem PEqualNP.Outside.L_meta_4671 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < x1 + x4.size → x5 < x1 + x4.size → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), PEqualNP.MetaComplexity.Monotone2 x9 ∧ x9.size = x4.size ∧ x9.output < x2 + x9.size ∧ x10 < x2 + x9.size ∧ ∀ (x11 : Fin x2 → Bool), x9.eval (List.ofFn x11) = x4.eval (List.ofFn (x11 ∘ x3)) ∧ (x9.wires (List.ofFn x11)).getD x10 Bool.false = (x4.wires (List.ofFn (x11 ∘ x3))).getD x5 Bool.false := by
  intro x1 x2 x3 x4 x5 hm ho h5
  refine ⟨⟨x4.gates.map (PEqualNP.Outside.L_meta_4671.rn x1 x2 x3),
      PEqualNP.Outside.L_meta_4671.phi x1 x2 x3 x4.output⟩,
    PEqualNP.Outside.L_meta_4671.phi x1 x2 x3 x5, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    simpa [PEqualNP.Outside.L_meta_4671.rn] using hm g0 hg0
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · have := PEqualNP.Outside.L_meta_4671.phi_lt x1 x2 x3 x4.size x4.output ho
    simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using this
  · have := PEqualNP.Outside.L_meta_4671.phi_lt x1 x2 x3 x4.size x5 h5
    simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using this
  · intro x11
    obtain ⟨m, _, _, hk⟩ := PEqualNP.Outside.L_meta_4671.inv_fold x1 x2 x3 x4.gates _ _
      (PEqualNP.Outside.L_meta_4671.inv_base x1 x2 x3 x11)
    exact ⟨hk x4.output, hk x5⟩
