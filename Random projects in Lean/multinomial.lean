import algebra.big_operators
import data.nat.choose

/-def pick' : ℕ → list ℕ → ℕ := λ n r, (nat.fact(n))/((finset.range(r.length)).prod(
    λ k, or.elim (classical.em(k < list.length r)) (λ h, r.nth_le k h) (_)
    ))-/
--def pick : ℕ → list ℕ → ℕ := λ n r, (nat.fact(n))/((finset.range(r.length)).prod(λ k, r.nth_le k (_)))
--def r : finset (list ℕ) := finset.map (_) (finset.range(numparts (n) (s.length)))
--def numparts (n : ℕ) (p : ℕ) := (nat.fact(n + p - 1))/((nat.fact(n))*(nat.fact(p - 1)))

def pick : ℕ → list ℕ → ℕ := 
    λ n r, if (list.sum r = n) then (nat.fact(n))/(list.prod(list.map nat.fact r)) else 0

variables {α : Type} [comm_semiring α] (s : list α) (n : ℕ)

-- take an array like [0, 0, 1, 0, 0, 0, 1, 1, 0] to [2, 3, 0, 1]
/-def stars_and_bars_inv : list ℕ → list ℕ := sorry

lemma binary_inj : function.injective (nat.to_digits 2) :=
    begin
        intros a b Hab,
        induction a,
        { induction b, refl,
          exfalso, rw nat.to_digits at b_ih, rw [nat.to_digits, nat.to_digits] at Hab, sorry },
        rw nat.to_digits at Hab, sorry,
    end

--set of all stars-and-bars versions of lists r_i
def r : finset (list ℕ) := finset.map (⟨nat.to_digits 2, binary_inj⟩) (finset.range(2 ^ (n + s.length - 1)))

def power_ith (i : ℕ) (l' : list ℕ) (Hsi : i < s.length) (Hls : l'.length = s.length): α := (s.nth_le i Hsi) ^ (l'.nth_le i (begin rw Hls, exact Hsi end))
def multinomial_summand (l' : list ℕ) : list α := pick n (stars_and_bars_inv(l')) * (list.prod(list.map(power_ith sorry l' sorry sorry)(list.range(s.length))))
theorem multinomial : (list.sum s)^n = finset.sum r (_)
-/
#check finset.filter

def r := ((add_monoid.smul n (multiset.range n.succ)).powerset.filter
  (λ k : multiset ℕ, k.sum = n ∧ k.card = s.length)).to_finset

#eval (let n := 3 in let r := 3 in
((add_monoid.smul n (multiset.range n.succ)).powerset.filter
  (λ s : multiset ℕ, s.sum = n ∧ s.card = r)).to_finset)

--theorem multinomial : (list.sum s)^n = finset.sum r (_)


/-def f {n : ℕ} : list α → α :=
    begin
        intro L, cases L with last sofar,
        { exact 0 },
        {

        }
    end-/