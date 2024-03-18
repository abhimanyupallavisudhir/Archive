import data.real.basic

def limit_right (f : ℝ → ℝ) (c : ℝ) (L : ℝ) := 
    ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 
    0 < x - c → x - c < δ → abs (f x - L) < ε

def limit_left (f : ℝ → ℝ) (c : ℝ) (L : ℝ) := 
    ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 
    0 < -(x - c) → -(x - c) < δ → abs (f x - L) < ε

def limit (f : ℝ → ℝ) (c : ℝ) (L : ℝ) :=
    ∀ ε > 0, ∃ δ : ℝ, ∀ x : ℝ, 
    0 < abs (x - c) → abs (x - c) < δ → abs (f x - L) < ε

lemma limit_right_iff_limit_left_of_reverse (f : ℝ → ℝ) (c : ℝ) (L : ℝ) (g : ℝ → ℝ) (Hfg : ∀ x, f x = g (2 * c - x))
: limit_right f c L ↔ limit_left g c L :=
begin
  have Hfg' : ∀ (x : ℝ), g x = f (2 * c - x), 
    intro x, have Hfg1 := Hfg (2 * c - x), simp at Hfg1, simp, exact Hfg1.symm,
  rw [limit_left, limit_right], split,
  { intros Hf ε He, have Hf1 := Hf ε He, cases Hf1 with δ Hf2, cases Hf2 with Hd Hf3, existsi δ, existsi Hd, 
    intro x, have Hf4 := Hf3 (2 * c - x), 
    simp only [two_mul, add_sub_cancel', sub_sub, add_sub_add_right_eq_sub] at Hf4, rw ←two_mul at Hf4,
    simp, rwa [←sub_eq_add_neg, Hfg'] },
  { intros Hg ε He, have Hg1 := Hg ε He, cases Hg1 with δ Hg2, cases Hg2 with Hd Hg3, existsi δ, existsi Hd,
    intro x, have Hg4 := Hg3 (2 * c - x),
    simp only [two_mul, add_sub_cancel', sub_sub, add_sub_add_right_eq_sub] at Hg4, rw ←two_mul at Hg4,
    simp at Hg4, rw Hfg, simp, exact Hg4 }
end

lemma limit_right_unique_of_ordered (f : ℝ → ℝ) (c : ℝ) (L1 : ℝ) (L2 : ℝ) (h_1 : L1 < L2) 
(HL1 : limit_right f c L1) (HL2 : limit_right f c L2) : false := 
begin
  have HL11 := HL1 ((L2 - L1)/2), have HL21 := HL2 ((L2 - L1)/2),
  have HL12 := HL11 (div_pos (sub_pos_of_lt h_1) two_pos), have HL22 := HL21 (div_pos (sub_pos_of_lt h_1) two_pos),
  cases HL12 with δ₁ HL13, cases HL22 with δ₂ HL23, cases HL13 with Hd1 HL14, cases HL23 with Hd2 HL24,
  have K0 : 0 < c + min (δ₁ / 2) (δ₂ / 2) - c,
    rw add_sub_cancel', apply lt_min (half_pos Hd1) (half_pos Hd2),
  have K1 : c + min (δ₁ / 2) (δ₂ / 2) - c < δ₁,
    rw add_sub_cancel', apply lt_of_le_of_lt (min_le_left (δ₁ / 2) (δ₂ / 2)) (half_lt_self Hd1),
  have K2 : c + min (δ₁ / 2) (δ₂ / 2) - c < δ₂,
    rw add_sub_cancel', apply lt_of_le_of_lt (min_le_right (δ₁ / 2) (δ₂ / 2)) (half_lt_self Hd2),
  have HL15 := HL14 (c + (min (δ₁ / 2) (δ₂ / 2))) K0 K1,
  have HL25 := HL24 (c + (min (δ₁ / 2) (δ₂ / 2))) K0 K2,
  rw abs_lt at HL15 HL25,
  have HL16 := HL15.2, have HL26 := HL25.1, simp at HL16 HL26,
  rw [add_div, add_comm (L2/2) _, ←add_assoc, neg_div, ←sub_eq_add_neg, sub_self_div_two] at HL16,
  rw [add_div, neg_div, ←sub_eq_add_neg, ←sub_eq_add_neg, ←sub_add, sub_self_div_two, add_comm] at HL26,
  revert HL16, exact not_lt_of_lt HL26,
end

theorem limit_right_unique (f : ℝ → ℝ) (c : ℝ) (L1 : ℝ) (L2 : ℝ) 
: limit_right f c L1 → limit_right f c L2 → L1 = L2 := 
begin
intros HL1 HL2, cases classical.em (L1 = L2), 
{ exact h },
{ exfalso, cases (lt_or_gt_of_ne h),
  { exact limit_right_unique_of_ordered f c L1 L2 h_1 HL1 HL2 },
  { exact limit_right_unique_of_ordered f c L2 L1 h_1 HL2 HL1 } }
end

lemma limit_left_unique_of_ordered (f : ℝ → ℝ) (c : ℝ) (L1 : ℝ) (L2 : ℝ) (h_1 : L1 < L2)
(HL1 : limit_left f c L1) (HL2 : limit_left f c L2) : false := sorry

theorem limit_left_unique (f : ℝ → ℝ) (c : ℝ) (L1 : ℝ) (L2 : ℝ) 
: limit_left f c L1 → limit_left f c L2 → L1 = L2 := sorry

theorem limit_unique_of_ordered (f : ℝ → ℝ) (c : ℝ) (L1 : ℝ) (L2 : ℝ) (h_1 : L1 < L2)
: limit f c L1 → limit f c L2 → L1 = L2 := sorry

theorem limit_unique (f : ℝ → ℝ) (c : ℝ) (L1 : ℝ) (L2 : ℝ) 
: limit f c L1 → limit f c L2 → L1 = L2 := sorry

theorem limit_right_unique' (f : ℝ → ℝ) (c : ℝ)
: ∃ L, limit_right f c L → ∃! L, limit_right f c L := sorry

theorem limit_left_unique' (f : ℝ → ℝ) (c : ℝ)
: ∃ L, limit_left f c L → ∃! L, limit_left f c L := sorry

theorem limit_unique' (f : ℝ → ℝ) (c : ℝ)
: ∃ L, limit f c L → ∃! L, limit f c L := sorry

theorem limit_exists_of_limits_equal (f : ℝ → ℝ) (c : ℝ) (L : ℝ) 
: limit_right f c L → limit_left f c L → limit f c L := sorry