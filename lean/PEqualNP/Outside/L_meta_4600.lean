import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4600

lemma getD_map_toNat (l : List (BitVec 59)) (i : ℕ) :
    (l.map BitVec.toNat).getD i 0 = (l.getD i 0).toNat := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

end PEqualNP.Outside.L_meta_4600

theorem PEqualNP.Outside.L_meta_4600 : have x1 : List (BitVec (59 : ℕ)) → Bool × Fin (40 : ℕ) × Fin (40 : ℕ) → List (BitVec (59 : ℕ)) := fun (x1 : List (BitVec (59 : ℕ))) (x2 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => x1 ++ [if x2.1 = Bool.true then x1.getD ↑x2.2.1 (0 : BitVec (59 : ℕ)) ||| x1.getD ↑x2.2.2 (0 : BitVec (59 : ℕ)) else x1.getD ↑x2.2.1 (0 : BitVec (59 : ℕ)) &&& x1.getD ↑x2.2.2 (0 : BitVec (59 : ℕ))]; have x2 : List ℕ → Bool × ℕ × ℕ → List ℕ := fun (x2 : List ℕ) (x3 : Bool × ℕ × ℕ) => x2 ++ [if x3.1 = Bool.true then x2.getD x3.2.1 (0 : ℕ) ||| x2.getD x3.2.2 (0 : ℕ) else x2.getD x3.2.1 (0 : ℕ) &&& x2.getD x3.2.2 (0 : ℕ)]; ∀ (x3 : List (BitVec (59 : ℕ))) (x4 : List (Bool × Fin (40 : ℕ) × Fin (40 : ℕ))), List.foldl x2 (List.map BitVec.toNat x3) (List.map (fun (x5 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => (x5.1, ↑x5.2.1, ↑x5.2.2)) x4) = List.map BitVec.toNat (List.foldl x1 x3 x4) := by
  intro x1 x2 x3 x4
  induction x4 generalizing x3 with
  | nil => rfl
  | cons o os ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [← ih]
    congr 1
    simp only [x1, x2, List.map_append, List.map_cons, List.map_nil]
    congr 2
    rcases o with ⟨b, i, j⟩
    cases b <;>
      simp only [PEqualNP.Outside.L_meta_4600.getD_map_toNat, BitVec.toNat_or, BitVec.toNat_and,
        Bool.false_eq_true, ↓reduceIte]
