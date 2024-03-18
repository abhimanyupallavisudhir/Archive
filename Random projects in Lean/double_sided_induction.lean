import data.int.basic
universe u

namespace int

theorem induction_on' {P : ℤ → Sort u} (z : ℤ) 
: P 0 → (∀ k ≥ 0, P k → P (k + 1)) → (∀ k ≤ 0, P k → P (k - 1)) → P z :=
λ H0 Hs Hp, int.rec_on z 
  (λ n, nat.rec_on n H0 (λ m ih, Hs m (of_nat_ge_zero _) ih))
  (λ n, nat.rec_on n
    (by rw [neg_succ_of_nat_coe', int.coe_nat_zero, neg_zero];
      exact Hp 0 (le_refl _) H0)
    (λ m ih, by rw [neg_succ_of_nat_coe']; rw [neg_succ_of_nat_coe] at ih;
      exact Hp _ (neg_nonpos_of_nonneg $ of_nat_ge_zero _) ih))

end int

def dumdum : ℕ → ℕ
| 0 := 0
| (nat.succ n) := 1 + dumdum n

#check nat.brec_on

#check @nat.rec_on



/-
namespace int

theorem induction_on {P : ℤ → Prop} (z : ℤ) 
: P 0 → (∀ k ≥ 0, P k → P (k + 1)) → (∀ k ≤ 0, P k → P (k - 1)) → P z :=
begin
  intros H0 Hs Hp,
  induction z with n n,
  { induction n with m ih, exact H0, 
    exact Hs m (of_nat_ge_zero _) ih },
  { induction n with m ih, 
      { rw [neg_succ_of_nat_coe', int.coe_nat_zero, neg_zero],
        exact Hp 0 (le_refl _) H0 },
      { rw [neg_succ_of_nat_coe'], rw [neg_succ_of_nat_coe] at ih,
        exact Hp _ (neg_nonpos_of_nonneg $ of_nat_ge_zero _) ih } }
end

end int
-/