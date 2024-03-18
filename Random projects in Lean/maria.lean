import .defs

lemma marias_destiny (n m : ℕ) : 
  { l : list (fin n) | l.length ≤ m }.finite := 
have HN : ∀ n : ℕ, n ≤ 0 ↔ n = 0 := λ n, ⟨nat.eq_zero_of_le_zero, le_of_eq⟩,
have HS : ∀ {α : Type} {y : α}, {x : α | x = y} = {y} :=
λ α y, set.ext (λ x, set.mem_singleton_iff.symm),
begin
  induction m with m ih,
  { simp only [HN, list.length_eq_zero, HS, set.finite_singleton] },
  conv { congr, congr, funext, rw [le_iff_eq_or_lt, nat.lt_succ_iff] },
  apply set.finite_union (_ : set.finite {l | _}) ih,
  generalize : nat.succ m = k, clear HN ih m,
  induction k with k ih,
  { simp only [list.length_eq_zero, HS, set.finite_singleton] },
  let f : list (fin n) × fin n → list (fin n) := 
    λ ⟨base, append⟩, list.cons append base,
  let S : set ((list (fin n)) × fin n) := 
    set.prod { base : list (fin n) | base.length = k } set.univ,
  have HR : {l | list.length l = nat.succ k} = f '' S,
    rw set.image,
    apply set.ext (λ l, ⟨λ hl, _, λ hb, _⟩),
    { cases l with hd tl,
      { exact false.elim (nat.succ_ne_zero _ (eq.trans rfl hl).symm) },
      refine ⟨⟨tl, hd⟩, ⟨_, _⟩⟩, 
      { simp only [S, set.prod, and_true, set.mem_univ, list.length, 
          set.mem_set_of_eq, nat.succ_eq_add_one] at ⊢ hl,
        exact eq_of_add_eq_add_right hl },
      refl },
    rcases hb with ⟨⟨tl, hd⟩, ⟨hm, hf⟩⟩,
    simp only [and_true, set.mem_univ, list.length, set.mem_set_of_eq, 
      and_true, set.mem_univ, list.length, set.prod_mk_mem_set_prod_eq, 
      set.mem_set_of_eq] at hm,
    simp only [hf.symm, f, list.length_cons, nat.succ_eq_add_one, 
      list.length, set.mem_set_of_eq, hm],
  rw HR,
  exact set.finite_image _ (set.finite_prod ih set.finite_univ)
end
