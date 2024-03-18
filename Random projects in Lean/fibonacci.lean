import tactic.norm_num

def fibN : ℕ → ℤ 
| 0 := 0
| 1 := 1
| (n + 2) := fibN n + fibN (n + 1)

def fibnN : ℕ → ℤ
| 0 := 1
| 1 := -1
| (n + 2) := fibnN n - fibnN (n + 1)

def lucN : ℕ → ℤ
| 0 := 2
| 1 := 1
| (n + 2) := lucN n + lucN (n + 1)

def lucnN : ℕ → ℤ
| 0 := -1
| 1 := 3
| (n + 2) := lucN n - lucN (n + 1)

def fib : ℤ → ℤ
| (int.of_nat n) := fibN n
| (int.neg_succ_of_nat n) := fibnN n

def luc : ℤ → ℤ
| (int.of_nat n) := lucN n
| (int.neg_succ_of_nat n) := lucnN n

variables (n m k r : ℤ) (Hr : r ≥ 0) (Hk2 : 2 ∣ k) (Hk3 : ¬ 3 ∣ k)

lemma fib_def : fib (n + 2) = fib (n + 1) + fib n :=
    begin
        cases n with n n,
        { rw [←one_add_one_eq_two, ←int.of_nat_one, ←int.of_nat_add, ←int.of_nat_add, ←int.of_nat_add,
            one_add_one_eq_two, fib, fib, fib, fibN, add_comm] },
        { sorry }
    end

lemma l1 : 2 * fib(m + n) = fib m * luc n + fib n * luc m := sorry
lemma l2 : 2 * luc(m + n) = 5 * fib m * fib n + luc m * luc n := sorry
lemma l3 : luc(2 * m) = luc(m) ^ 2 + (-1)^(int.nat_abs(m - 1)) * 2 := sorry
lemma l4 : int.gcd (fib(3 * m)) (luc(3 * m)) = 2 := sorry
lemma l5 : ¬ 3 ∣ n → int.gcd (fib n) (luc n) = 1 := sorry
lemma l6 : 2 ∣ (luc m) ↔ 3 ∣ m := sorry
lemma l7 : 3 ∣ (luc m) ↔ m % 4 = 2 := sorry
lemma l8 : fib (- n) = (-1)^(int.nat_abs(n - 1)) * fib (n) := sorry
lemma l9 : luc (- n) = (-1)^(int.nat_abs(n - 1)) * luc (n) := sorry
lemma l10 : luc (k) % 4 = 3 := sorry
lemma l11 : luc (m + 2 * k) % luc (k) = - luc (m) := sorry
lemma l13 : luc (m + 12) % 8 = luc (m) := sorry

theorem t1 : (∃ x, luc n = x ^ 2) → (n = 1 ∨ n = 3) := sorry

theorem t2 : (∃ x, luc n = 2 * x ^ 2) → (n = 0 ∨ n = 6 ∨ n = - 6) := sorry

theorem t3 : (∃ x, fib n = x ^ 2) → (n = 0 ∨ n = 2 ∨ n = 12 ∨ n = 1 ∨ n = -1) := sorry

/-
def fibL : ℤ → ℤ
| (int.of_nat n) := fibN n
| (int.neg_succ_of_nat n) := ((-1)^n * fibN (nat.succ n))

def luc : ℤ → ℤ
| (int.of_nat n) := lucN n
| (int.neg_succ_of_nat n) := ((-1)^n * lucN (nat.succ n))


--set_option pp.all true
lemma fib_defn (z : ℤ) : fib (z) = fib (z - 1) + fib (z - 2) :=
begin
    cases z with n n,
    --case nat n
        cases classical.em (int.of_nat n - 1 ≥ 0),
        --case nat nl1
            have enl1 := int.eq_coe_of_zero_le h, cases enl1 with nl1 hnl1, rw [hnl1, ←int.of_nat_eq_coe, fib, fib],
            cases classical.em (int.of_nat n - 2 ≥ 0),
            --case nat nl2
                have enl1 := int.eq_coe_of_zero_le (h_1), cases enl1 with nl2 hnl2, rw [hnl2, ←int.of_nat_eq_coe nl2, fib, ←int.coe_nat_add, int.coe_nat_eq_coe_nat_iff],
                have h' : 0 ≤ int.of_nat n - 1 := h, rw [@le_sub ℤ _ 0 (int.of_nat n) 1, sub_zero, ←int.coe_nat_one, int.of_nat_eq_coe, int.coe_nat_le] at h',
                have h_1' : 0 ≤ int.of_nat n - 2 := h_1, rw [@le_sub ℤ _ 0 (int.of_nat n) 2, sub_zero, ←one_add_one_eq_two, ←int.coe_nat_one, ←int.coe_nat_add, int.of_nat_eq_coe, int.coe_nat_le, one_add_one_eq_two] at h_1',
                rw [int.of_nat_eq_coe, ←int.coe_nat_one, ←int.coe_nat_sub h',  int.coe_nat_eq_coe_nat_iff] at hnl1,
                rw [int.of_nat_eq_coe, ←one_add_one_eq_two, ←int.coe_nat_one, ←int.coe_nat_add, one_add_one_eq_two, ←int.coe_nat_sub h_1', int.coe_nat_eq_coe_nat_iff] at hnl2,
                have hduh : n - 1 = n - 2 + 1,
                    induction n,
                    --case 0 (this is stupid... this is so stupid)
                        revert h', norm_num,
                    --case succ
                        
                --rw [←@nat.sub_add_cancel n 2 (h_1'), ←hnl1, ←hnl2],

end
-/

#check @le_sub 

#check int.of_nat_succ
#check int.coe_nat_sub
#check int.eq_neg_succ_of_lt_zero
#check int.exists_eq_neg_of_nat
#check int.eq_coe_of_zero_le

#check lt_iff_not_ge

/-lemma l1 (M : ℤ) (N : ℤ) : 2 * (fib (M + N)) = fib (M) * luc (N) + fib (N) * luc (M) :=
    begin
        cases M, 
          cases N,
            apply nat.strong_induction_on N, intros s lesss,
            apply nat.strong_induction_on M, intros t lesst,
            

        /-have hs : (∀ s t : ℕ, s ≤ m ∧ t ≤ n → 2 * fib (s + t) = fib s * luc t + fib t * luc s),
        induction n,
        --base n
            induction m,
            --base m-/



        /-induction n,
        --base
            induction m,
            --base
                intros s t pl, cases pl with pls plt, rw le_zero_iff_eq at pls plt, rw [plt, pls, fib, luc], refl,
            --succ
                intros s t pl, cases pl with pls plt, rw le_zero_iff_eq at plt, rw [plt, fib, luc, mul_comm], simp,
        --succ
            induction m,
            --base
                intros s t pl, cases pl with pls plt, rw le_zero_iff_eq at pls, rw [pls, fib, luc, mul_comm], simp,
            --succ
                intros s t pl, cases pl with pls plt,
                rw [←nat.lt_succ_iff, nat.lt_succ_iff_lt_or_eq, nat.lt_succ_iff] at pls plt,
                cases pls,
                --case s le
                    cases plt,
                    --case t le-/
                    
    end

#check nat.lt_succ_iff
#check nat.lt_succ_iff_lt_or_eq


/-begin
induction m,
--base
    induction n, 
    --base
        rw [fib, luc], refl,
    --succ
        rw [fib, luc], simp, rw mul_comm,
--succ
    induction n,
    --base
        rw [fib, luc], simp, rw mul_comm,
    --succ
        rw [nat.succ_eq_add_one, nat.succ_eq_add_one], simp, rw ←add_assoc, 
        rw fib,
end-/

#check nat.succ_eq_add_one
#check nat.strong_induction_on
#check nat.succ_pred_eq_of_pos
-/