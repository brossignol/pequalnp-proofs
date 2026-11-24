import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4779 : ∀ (x1 : List (ℕ × ℕ)) (x2 : (Fin (14 : ℕ) → Bool) → Bool), ((0 : ℕ), (7 : ℕ)) ∈ x1 → (∀ (x4 x5 : Fin (14 : ℕ) → Bool), (∀ (x6 : Fin (14 : ℕ)), x4 x6 = Bool.true → x5 x6 = Bool.true) → x2 x4 = Bool.true → x2 x5 = Bool.true) → (∀ (x5 : Fin (14 : ℕ) → Bool), (¬∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ x1 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (∀ (x7 : Fin (14 : ℕ)), x5 x7 = Bool.false → ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x1 ∧ Function.update x5 x7 Bool.true x9 = Bool.true ∧ Function.update x5 x7 Bool.true x10 = Bool.true) → x5 (0 : Fin (14 : ℕ)) = Bool.false ∨ x5 (7 : Fin (14 : ℕ)) = Bool.false → x2 x5 ≠ Bool.true) → ∀ (x6 : Fin (14 : ℕ) → Bool), x2 x6 = Bool.true → ∃ (x8 : Fin (14 : ℕ)) (x9 : Fin (14 : ℕ)), (↑x8, ↑x9) ∈ x1 ∧ x6 x8 = Bool.true ∧ x6 x9 = Bool.true := by
  classical
  intro E g h07 hmono hmax y hy
  by_contra hind
  -- the independent supersets of `y`
  let S : Finset (Fin 14 → Bool) := Finset.univ.filter fun z =>
    (∀ i, y i = true → z i = true) ∧
      ¬∃ (a b : Fin 14), ((a : ℕ), (b : ℕ)) ∈ E ∧ z a = true ∧ z b = true
  have hyS : y ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ h => h, hind⟩
  -- take one with the most true coordinates
  obtain ⟨z, hzS, hzmax⟩ := S.exists_max_image
    (fun z => (Finset.univ.filter fun i => z i = true).card) ⟨y, hyS⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hzS
  obtain ⟨hyz, hzind⟩ := hzS
  apply hmax z hzind
  · -- `z` is maximal: adding any vertex creates an edge
    intro v hv
    by_contra hno
    set z' := Function.update z v true with hz'
    have hz'S : z' ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun i hi => ?_, hno⟩
      by_cases hiv : i = v
      · subst hiv; simp [z']
      · simp [z', Function.update_of_ne hiv, hyz i hi]
    have hle := hzmax z' hz'S
    have hlt : (Finset.univ.filter fun i => z i = true).card <
        (Finset.univ.filter fun i => z' i = true).card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨v, ?_, ?_⟩
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        by_cases hiv : i = v
        · subst hiv; simp [z']
        · simp [z', Function.update_of_ne hiv, hi]
      · simp [z']
      · simp [hv]
    omega
  · -- an independent set cannot contain both ends of the edge 0–7
    by_contra h
    push Not at h
    simp only [ne_eq, Bool.not_eq_false] at h
    exact hzind ⟨0, 7, by simpa using h07, h.1, h.2⟩
  · exact hmono y z hyz hy
