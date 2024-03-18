import data.complex.exponential
import analysis.exponential

open real

-- n'th root of x
noncomputable definition nth_root (x : ℝ) (n : ℕ) (Hxpos : 0 < x) (Hnpos : 0 < n)
: ℝ := exp ((log x) / n)

variables (x : ℝ) (y : ℝ) (n : ℕ) (Hxpos : 0 < x) (Hypos : 0 < y) (Hnpos : 0 < n)

theorem pow_lt (Hxy : x < y) (Hxpos : 0 < x) (Hypos : 0 < y) (Hnpos : 0 < n) : x ^ n < y ^ n :=
    begin
        rw ←nat.sub_add_cancel Hnpos,
        induction (n - 1), simp, exact Hxy,
        rw [pow_add, pow_add, nat.succ_eq_add_one], simp,
        apply mul_lt_mul ih (le_of_lt Hxy) Hxpos (le_of_lt (pow_pos Hypos _)),
    end

theorem pow_eq (Hxpos : 0 < x) (Hypos : 0 < y) (Hnpos : 0 < n) : x ^ n = y ^ n → x = y :=
    begin
        intro, by_contradiction b,
        cases (lt_or_gt_of_ne b),
        { have hn : x ^ n < y ^ n, apply pow_lt x y n h Hxpos Hypos Hnpos,
            apply ne_of_lt hn a },
        { have hn : y ^ n < x ^ n, apply pow_lt y x n h Hypos Hxpos Hnpos,
            apply ne_of_gt hn a },
    end

theorem exp_mul : ∀ n : ℕ, exp(n*x) = (exp(x))^n
| 0 := by simp
| (nat.succ n) := by rw [pow_succ', nat.cast_add_one, add_mul, exp_add, ←exp_mul, one_mul]

theorem nth_root_pos : nth_root x n Hxpos Hnpos > 0 := real.exp_pos ((log x) / n)

theorem nth_root_power : (nth_root x n Hxpos Hnpos) ^ n = x := 
    begin
        rw [nth_root, ←exp_mul, mul_div_cancel', exp_log Hxpos],
        rw [nat.cast_ne_zero], apply ne_of_gt Hnpos,
    end

theorem nth_root_unique (Hxpos : 0 < x) (Hypos : 0 < y) (Hnpos : 0 < n) : y ^ n = x → y = nth_root x n Hxpos Hnpos :=
    begin
        intro,
        have b : (nth_root x n Hxpos Hnpos)^n = x := nth_root_power _ _ _ _,
        have ab : y^n = nth_root x n Hxpos Hnpos ^ n := eq.trans a b.symm,
        apply pow_eq _ _ _ Hypos (nth_root_pos _ _ _ _) Hnpos ab,
    end

open complex

theorem polar_form (z : ℂ) : z = (complex.abs z) * exp (arg z * I) :=
    begin
        cases classical.em (z = 0),
        { rw h, simp },
        { rw [exp_mul_I, ←re_add_im(cos ↑(arg z)), cos_of_real_im, ←re_add_im(sin ↑(arg z)), sin_of_real_im, 
            ←real.cos, ←real.sin, mul_add, mul_add, of_real_zero, add_mul, zero_mul, zero_mul, mul_zero, add_zero, add_zero, 
            ←mul_assoc, ←of_real_mul, ←of_real_mul, cos_arg, sin_arg, mul_div_cancel', mul_div_cancel', re_add_im],
          show ¬(abs z = 0), rw complex.abs_eq_zero, exact h,
          show ¬(abs z = 0), rw complex.abs_eq_zero, exact h,
          exact h },
    end

variables (θ ψ : ℝ)

definition equal_angle := ∃ k : ℤ, θ - ψ = 2 * pi * k
definition semiequal_angle_even := ∃ k : ℤ, θ + ψ = 2 * k * pi
definition semiequal_angle_odd := ∃ k : ℤ, θ + ψ = (2 * k + 1) * pi

theorem equal_angle.equiv : equivalence equal_angle := sorry -- Jean Lo

theorem cos_sub_cos : real.cos θ - cos ψ = -2 * sin((θ + ψ)/2) * sin((θ - ψ)/2) :=
    begin
        have c1 := real.cos_add ((θ + ψ) / 2) ((θ - ψ) / 2),
        have c2 := real.cos_sub ((θ + ψ) / 2) ((θ - ψ) / 2),
        rw [div_add_div_same, add_sub] at c1, 
        rw [div_sub_div_same, ←sub_add] at c2,
        simp at c1 c2,
        rw [c1, c2], simp, rw ←mul_two, simp, rw [mul_comm, mul_assoc],
    end

theorem sin_sub_sin : real.sin θ - sin ψ = 2 * sin((θ - ψ)/2) * cos((θ + ψ)/2) :=
    begin
        have s1 := real.sin_add ((θ + ψ) / 2) ((θ - ψ) / 2),
        have s2 := real.sin_sub ((θ + ψ) / 2) ((θ - ψ) / 2),
        rw [div_add_div_same, add_sub] at s1, 
        rw [div_sub_div_same, ←sub_add] at s2,
        simp at s1 s2,
        rw [s1, s2], simp, rw ←mul_two, simp, rw [mul_comm, mul_comm (real.cos ((θ + ψ) / 2)), mul_assoc],
    end

--theorem cos_eq_sin_pi_div_two_sub : real.cos θ = sin (pi/2 - θ) := begin rw real.sin_sub (pi/2) θ, norm_num end
--theorem sin_eq_cos_pi_div_two_sub : real.sin θ = cos (pi/2 - θ) := begin rw real.cos_sub (pi/2) θ, norm_num end

theorem cos_eq_zero_iff : real.cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * k + 1) * pi / 2 := 
    begin
        split,
        { rw [←real.sin_pi_div_two_sub, sin_eq_zero_iff], intro, cases a with n hn, 
          existsi -n, rwa [int.cast_neg, add_mul, add_div, mul_assoc, mul_div_cancel_left, one_mul,
                          ←neg_mul_eq_neg_mul, eq_neg_add_iff_add_eq, ←eq_sub_iff_add_eq], norm_num },

        { intro, cases a with n hn, rw [←real.sin_pi_div_two_sub, hn, add_mul, add_div, mul_assoc, 
                                          mul_div_cancel_left, one_mul, sub_add_eq_sub_sub_swap, sub_self, 
                                          zero_sub, real.sin_neg, neg_eq_zero, sin_eq_zero_iff], 
          existsi n, refl, norm_num },
    end

theorem cos_eq_if (Hcos : real.cos θ = cos ψ) : equal_angle θ ψ ∨ semiequal_angle_even θ ψ :=
    begin
        rw [←sub_eq_zero, cos_sub_cos] at Hcos, simp at Hcos, 
        cases Hcos,
        { cases Hcos,
          { exfalso, revert Hcos, norm_num },
          { right, 
            rw sin_eq_zero_iff at Hcos, cases Hcos with n Hcos, 
            rw [eq_comm, div_eq_iff_mul_eq, mul_comm, ←mul_assoc, eq_comm] at Hcos, 
            existsi n, exact Hcos, norm_num },
        },
        { left,
          rw sin_eq_zero_iff at Hcos, cases Hcos with n Hcos,
          rw [←sub_eq_add_neg, eq_comm, div_eq_iff_mul_eq, mul_comm, mul_comm _ pi, ←mul_assoc, eq_comm] at Hcos,
          existsi n, exact Hcos, norm_num },
    end

theorem sin_eq_if (Hsin : real.sin θ = sin ψ) : equal_angle θ ψ ∨ semiequal_angle_odd θ ψ :=
    begin
        rw [←sub_eq_zero, sin_sub_sin] at Hsin, simp at Hsin, 
        cases Hsin,
        { cases Hsin, 
          { exfalso, revert Hsin, norm_num },
          { left,
            rw sin_eq_zero_iff at Hsin, cases Hsin with n Hsin,
            rw [eq_comm, div_eq_iff_mul_eq, mul_comm _ pi, mul_comm, ←mul_assoc, eq_comm, ←sub_eq_add_neg] at Hsin, 
            existsi n, exact Hsin, norm_num },
        },
        { right,
          rw cos_eq_zero_iff at Hsin, cases Hsin with n Hsin,
          rw [eq_comm, div_eq_iff_mul_eq, div_mul_cancel] at Hsin, 
          existsi n, exact Hsin, norm_num, norm_num },
    end


theorem cos_sin_inj (Hcos : real.cos θ = cos ψ) (Hsin : real.sin θ = sin ψ) : equal_angle θ ψ :=
    begin
        have Hcos' := cos_eq_if _ _ Hcos, have Hsin' := sin_eq_if _ _ Hsin,
        cases Hcos',
        { exact Hcos' },
        { cases Hsin',
          { exact Hsin' },
          { exfalso,
            cases Hcos' with c Hc, cases Hsin' with s Hs, rw Hc at Hs,
            have H : ∃ k : ℤ, 2 * k = 1, 
            { existsi (c - s), 
              rw [←@int.cast_inj ℝ _ _ _, int.cast_mul, int.cast_sub, int.cast_bit0, int.cast_one, mul_sub,
                  sub_eq_iff_eq_add'], apply @eq_of_mul_eq_mul_right _ _ pi _ _ (ne_of_gt pi_pos), exact Hs },
            cases H with k Hk, have H' := dvd.intro k Hk, revert H', 
            rw [←int.coe_nat_one, ←linarith.int.coe_nat_bit0, int.coe_nat_dvd], norm_num } }
    end

theorem polar_form_unique (z : ℂ) (r θ : ℝ) (Hr : r ≥ 0) (H : z ≠ 0) (H2 : z = r * exp (θ * I)) :
r = complex.abs z ∧ equal_angle θ (arg z) := 
    begin
        have Hr' : r > 0,
        { apply lt_of_le_of_ne Hr,
          intro, rw [←a, of_real_zero, zero_mul] at H2, apply H H2 },
        split,
        { rw [H2, complex.abs_mul, exp_mul_I, abs_cos_add_sin_mul_I, mul_one], 
          exact (complex.abs_of_nonneg Hr).symm },
        { rw [H2, arg_real_mul _ Hr'], sorry }
    end

theorem de_moivre (n : ℕ) (z: ℂ) : (cos (z) + I * sin(z)) ^ n = cos (↑n * z) + I * sin(↑n * z) := 
    begin
        induction n, simp,
        rw [pow_succ, n_ih, nat.succ_eq_add_one, nat.cast_add, add_mul, add_mul, nat.cast_one, one_mul,
        complex.cos_add, complex.sin_add], simp,
        rw [mul_comm, mul_add, ←mul_assoc, mul_comm I (sin z), mul_assoc (sin z) I I, I_mul_I, 
            mul_comm (sin z) (-1), neg_one_mul, add_mul, mul_add, ←add_assoc, ←add_assoc, ←add_assoc, ←mul_assoc,
            ←mul_assoc, mul_comm _ (sin z), neg_mul_eq_neg_mul, mul_comm _ I, mul_assoc I (sin z) _, 
            mul_comm (sin z) _, ←mul_assoc, add_assoc, add_comm (I * cos (↑n_n * z) * sin z) _, add_assoc, 
            add_comm (I * sin (↑n_n * z) * cos z) _, ←add_assoc (cos (↑n_n * z) * cos z) _, ←add_assoc], 
    end

theorem nth_roots_of_unity (z : ℂ) (n : ℕ) (Hpos : n > 0) :
z ^ n = 1 ↔ ∃ j : ℕ, j < n ∧ z = exp (I * 2 * real.pi / n) ^ j := sorry

theorem complex.nth_roots (z : ℂ) (Hz : z ≠ 0) (n : ℕ) (Hnpos : n > 0) (w : ℂ) (Hw : w ^ n = z) :
complex.abs w = nth_root (complex.abs z) n (complex.abs_pos_of_nonzero z Hz) Hnpos
∧ ∃ j : ℕ, j < n ∧ equal_angle (arg z / n) (arg w + 2 * pi / j) := sorry

