import data.real.basic data.nat.prime data.real.irrational data.padics.padic_norm data.polynomial
open rat real

--goes in int, rename to `nat_abs_pow`
lemma int_o_nat_abs_pow (n : ℤ) (k : ℕ) : int.nat_abs (n ^ k) = (int.nat_abs n) ^ k :=
begin
  induction k,
  rw [pow_zero, nat.pow_zero, int.nat_abs_one],
  rw [pow_succ', int.nat_abs_mul, nat.pow_succ, k_ih],
end

--goes in rat, rename to `cast_pow`
lemma cast_pow (k : ℕ) (q : ℚ) : ((q ^ k : ℚ) : ℝ) = q ^ k := by induction k; simp [*, rat.cast_mul, pow_succ]

--goes in padic_val_rat, rename to `pow`
lemma padic_val_rat_o_pow (p : ℕ) (k : ℕ) [p_prime : nat.prime p] {q : ℚ} [q_nz : q ≠ 0] :
    padic_val_rat p (q ^ k) = k * padic_val_rat p q :=
begin
  induction k,
  rw [pow_zero, int.coe_nat_zero, zero_mul, padic_val_rat.one p_prime.gt_one],
  rw [pow_succ', padic_val_rat.mul (p)(pow_ne_zero(k_n)(q_nz))(q_nz), k_ih], simp, 
  have h : (1 * padic_val_rat p q + ↑k_n * padic_val_rat p q = (1 + ↑k_n) * padic_val_rat p q), rw [←int.coe_nat_one, add_mul],
  rw one_mul at h, exact h,
end

--theorem irr_of_notint_poly_root

theorem irr_nrt_of_notint_nrt' {x : ℝ} (n : ℕ) (m : ℤ)
  (hxr : x ^ n = m) (hv : ¬ ∃ y : ℤ, x = y) (hnpos : n > 0) :
  irrational x
| ⟨q, e⟩ := begin
  rw [e, ←cast_pow] at hxr, cases q with N D P C,
  have c1 : ((D : ℤ) : ℝ) ≠ 0,
  { rw [int.cast_ne_zero, int.coe_nat_ne_zero], exact ne_of_gt P },
  have c2 : ((D : ℤ) : ℝ) ^ n ≠ 0 := pow_ne_zero _ c1,
  rw [num_denom', cast_pow, cast_mk, div_pow _ c1, div_eq_iff_mul_eq c2,
      ←int.cast_pow, ←int.cast_pow, ←int.cast_mul, int.cast_inj] at hxr,
  have hdivn : ↑D ^ n ∣ N ^ n := dvd.intro_left m hxr,
  rw [←int.dvd_nat_abs, ←int.coe_nat_pow, int.coe_nat_dvd, int.nat_abs_pow, nat.pow_dvd_pow_iff hnpos] at hdivn,
  have hdivn' : nat.gcd N.nat_abs D = D := nat.gcd_eq_right hdivn,
  refine hv ⟨N, _⟩,
  rwa [num_denom', ←hdivn', C.gcd_eq_one, int.coe_nat_one, mk_eq_div,
      int.cast_one, div_one, cast_coe_int] at e
end

theorem irr_nrt_of_notint_nrt (x : ℝ) (n : ℕ) (m : ℤ)
        (hxr : x ^ n = m) (hv : ¬ (∃ y : ℤ, x = ↑y)) (hnpos : n > 0) (hmpos : m > 0) :
        irrational x
| ⟨q, e⟩ := begin
  rw [e, ←cast_pow] at hxr, cases q,
  have c1 : ((q_denom : ℤ) : ℝ) ≠ 0, rw [int.cast_ne_zero, int.coe_nat_ne_zero], apply ne_of_gt(q_pos),
  have c2 : (((q_denom ^ n) : ℤ) : ℝ) ≠ 0, rw int.cast_ne_zero, apply pow_ne_zero, rw int.coe_nat_ne_zero, apply ne_of_gt(q_pos),
  have c3 : q_denom ≠ 1, intro, rw [rat.num_denom', a, mk_eq_div, int.coe_nat_one, int.cast_one, div_one, cast_coe_int] at e, apply hv, existsi q_num, exact e,
  rw [num_denom', cast_pow, cast_mk, div_pow, ←int.cast_pow, ←int.cast_pow, div_eq_iff_mul_eq, ←int.cast_mul, int.cast_inj] at hxr, swap, exact c2, swap, exact c1,
  have hdivn : (↑q_denom ^ n) ∣ (q_num)^n, apply dvd.intro_left m hxr,
  rw [←int.dvd_nat_abs, ←int.coe_nat_pow, int.coe_nat_dvd, int_o_nat_abs_pow, nat.pow_dvd_pow_iff hnpos] at hdivn,
  have hdivn' : nat.gcd (int.nat_abs q_num) (q_denom) = q_denom, apply nat.gcd_eq_right hdivn,
  have hint : q_denom = 1, rw ←hdivn', apply nat.coprime.gcd_eq_one q_cop,
  apply c3, exact hint,
end

theorem irr_nrt_of_n_not_dvd_padic_val (x : ℝ) (n : ℕ) (m : ℤ) (p : ℕ) 
        [hp : nat.prime p] (hxr : x ^ n = m) (hv : padic_val p m % n ≠ 0) (hnpos : n > 0) (hmpos : m > 0) :
        irrational x
| ⟨q, e⟩ := begin
  rw [e, ←cast_coe_int, ←cast_pow, cast_inj] at hxr,
  have : padic_val_rat p (q ^ n) % n = padic_val_rat p (↑m) % n := by rw hxr,
  have hqnz : q ≠ 0, {rintro rfl, rw [zero_pow (hnpos), eq_comm, int.cast_eq_zero] at hxr, revert hxr, exact ne_of_gt hmpos},
  rw [padic_val_rat.padic_val_rat_of_int hp.gt_one, ← int.coe_nat_mod, @padic_val_rat_o_pow p n _ _ hqnz, int.mul_mod_right, 
  eq_comm, int.coe_nat_eq_zero] at this,
  apply hv, exact this,
end

theorem irr_sqrt_of_padic_val_odd (m : ℤ) (Hnpl : m > 0)
  (p : ℕ) [hp : nat.prime p] (Hpv : padic_val p m % 2 = 1) :
  irrational (sqrt m)
| ⟨q, e⟩ := begin
  have hqm := mul_self_sqrt (le_of_lt (int.cast_lt.2 Hnpl)),
  rw [e, ← cast_mul, ← cast_coe_int, @cast_inj ℝ] at hqm,
  have : padic_val_rat p (q * q) % 2 = padic_val_rat p m % (2:ℕ), { rw hqm, refl },
  have hq : q ≠ 0, { rintro rfl, exact ne_of_lt Hnpl (int.cast_inj.1 hqm) },
  rw [padic_val_rat.padic_val_rat_of_int hp.gt_one, ← int.coe_nat_mod, Hpv,
      padic_val_rat.mul p hq hq, ← mul_two, int.mul_mod_left] at this,
  exact zero_ne_one this
end

theorem irr_sqrt_of_padic_val_odd' (m : ℤ) (Hnpl : m > 0) 
                                  (Hpn : ∃ p : ℕ, nat.prime p ∧ (padic_val p m) % 2 = 1) : 
        irrational (sqrt (↑m)) 
| ⟨⟨n, d, h, c⟩, e⟩ := begin
  cases Hpn with p Hpp, cases Hpp with Hp Hpv,
  simp [num_denom', mk_eq_div] at e,
  have Hnpl' : 0 < (m : ℝ) := int.cast_pos.2 Hnpl,
  have Hd0 : (0:ℝ) < d := nat.cast_pos.2 h,
  have := mul_self_sqrt (le_of_lt Hnpl'),
  rw [e, div_mul_div, div_eq_iff_mul_eq (ne_of_gt (mul_pos Hd0 Hd0)), ←int.cast_mul, ←int.cast_of_nat, 
      ←int.cast_mul, ←int.cast_mul m (int.of_nat d * int.of_nat d), int.cast_inj] at this,
  have d0' : int.of_nat d ≠ 0, rw [←int.coe_nat_eq, int.coe_nat_ne_zero], apply ne_of_gt h,
  have n0 : n ≠ 0, intro y0, rw [y0, int.cast_zero, zero_div, sqrt_eq_zero'] at e, revert e, apply not_le_of_gt Hnpl',
  have HPV : padic_val p (m * (int.of_nat d * int.of_nat d)) = padic_val p (n * n), rw this,
  rw [←padic_val.mul Hp (ne_of_gt Hnpl) (mul_ne_zero d0' d0'), ←padic_val.mul Hp d0' d0', 
      ←padic_val.mul Hp n0 n0, ←mul_two, ←mul_two] at HPV,
  have HPV' : (padic_val p m + padic_val p (int.of_nat d) * 2) % 2 = (padic_val p n * 2) % 2, rw HPV,
  rw [nat.mul_mod_left, nat.add_mul_mod_self_right, Hpv] at HPV',
  revert HPV', exact dec_trivial,
end

theorem irr_sqrt_of_padic_val_odd'' (m : ℤ) (Hnpl : m > 0)
  (Hpn : ∃ (p : ℕ) [nat.prime p], (padic_val p m) % 2 = 1) :
  irrational (sqrt m) := sorry

theorem irr_of_sqrt_prime (p : ℕ) (Hp : nat.prime p) : irrational(sqrt(↑p)) :=
begin
rw ←int.cast_coe_nat, apply irr_sqrt_of_padic_val_odd p (int.coe_nat_pos.2(@gt_trans ℕ _ p 1 0 (nat.prime.gt_one Hp)(nat.one_pos))),
existsi [p, Hp], rw padic_val.padic_val_self(nat.prime.gt_one Hp), exact dec_trivial,
end

theorem irr_sqrt_two : irrational (sqrt 2) := irr_of_sqrt_prime 2 nat.prime_two

theorem irr_sqrt_nat_of_padic_val_odd (m : ℕ) (Hnpl : m > 0) 
                                  (Hpn : ∃ p : ℕ, nat.prime p ∧ (padic_val p ↑m) % 2 = 1) : 
        irrational (sqrt (↑m)) 
| ⟨⟨n, d, h, c⟩, e⟩ := begin
  rcases Hpn with ⟨p, Hp, Hpv⟩, resetI,
  simp [num_denom', mk_eq_div] at e,
  have Hnpl' : 0 < (m : ℝ) := nat.cast_pos.2 Hnpl,
  have Hd0 : (0:ℝ) < d := nat.cast_pos.2 h,
  have := mul_self_sqrt (le_of_lt Hnpl'),
  rw [e, div_mul_div, div_eq_iff_mul_eq (ne_of_gt (mul_pos Hd0 Hd0)), ←int.cast_mul, ←int.cast_of_nat, ←int.cast_of_nat,
      ←int.cast_mul, ←int.cast_mul (int.of_nat m) (int.of_nat d * int.of_nat d), int.cast_inj] at this,
  have d0' : int.of_nat d ≠ 0, rw [←int.coe_nat_eq, int.coe_nat_ne_zero], apply ne_of_gt h,
  have n0 : n ≠ 0, intro y0, rw [y0, int.cast_zero, zero_div, sqrt_eq_zero'] at e, revert e, apply not_le_of_gt Hnpl',
  have HPV : padic_val p (int.of_nat m * (int.of_nat d * int.of_nat d)) = padic_val p (n * n), rw this,
  rw [←int.coe_nat_eq, ←padic_val.mul Hp (ne_of_gt (int.coe_nat_pos.2(Hnpl))) (mul_ne_zero d0' d0'), ←padic_val.mul Hp d0' d0', 
      ←padic_val.mul Hp n0 n0, ←mul_two, ←mul_two] at HPV,
  have HPV' : (padic_val p m + padic_val p (int.of_nat d) * 2) % 2 = (padic_val p n * 2) % 2, rw HPV,
  rw [nat.mul_mod_left, nat.add_mul_mod_self_right, Hpv] at HPV',
  cases HPV'
end

def rat_o_pow (q : ℚ) (k : ℕ) : ℚ :=
{ num   := (q.num) ^ k, 
  denom := (q.denom) ^ k,
  pos   := nat.pow_pos q.pos k,
  cop   := by rw int_o_nat_abs_pow; apply nat.coprime.pow; exact q.cop }


--goes in int, rename to `one_mul`
theorem int_o_one_mul (n : ℤ) : 1 * n = n :=
begin
  induction n,
  rw [←int.coe_nat_one, int.of_nat_eq_coe, ←int.coe_nat_mul, int.coe_nat_inj', nat.one_mul],
  rw [int.neg_succ_of_nat_coe, ←int.coe_nat_one, mul_neg_eq_neg_mul_symm, ←int.coe_nat_mul, nat.one_mul],
end