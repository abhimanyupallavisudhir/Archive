import order.filter.basic

--------------------ALGEBRA.ORDERED_GROUP--------------------

lemma neg_neg_iff_pos {α : Type} [_inst_1 : ordered_comm_group α] {a : α} : -a < 0 ↔ 0 < a := ⟨ pos_of_neg_neg, neg_neg_of_pos ⟩

--------------------ALGEBRA.FIELD--------------------

instance division_ring_has_div' {α : Type} [division_ring α] : has_div α :=
⟨algebra.div⟩

@[simp] lemma inv_eq_zero {α : Type} [discrete_field α] (a : α) : a⁻¹ = 0 ↔ a = 0 :=
classical.by_cases (assume : a = 0, by simp [*])(assume : a ≠ 0, by simp [*, inv_ne_zero])

--------------------DATA.SET.BASIC--------------------

namespace set

lemma set_of_eq_eq_singleton {α : Type} {m : α} : {n | n = m} = {m} := set.ext $ λ n, (set.mem_singleton_iff).symm

end set

--------------------ORDER.FILTER.BASIC--------------------

namespace filter

open filter

variables {α : Type}

lemma cofinite_ne_bot (hi : set.infinite (@set.univ α)) : @cofinite α ≠ ⊥ :=
forall_sets_neq_empty_iff_neq_bot.mp 
  $ λ s hs hn, by change set.finite _ at hs; 
    rw [hn, set.compl_empty] at hs; exact hi hs

/-- Ultrafilter extending the cofinite filter -/
noncomputable def hyperfilter : filter α := ultrafilter_of cofinite

lemma hyperfilter_le_cofinite (hi : set.infinite (@set.univ α)) : @hyperfilter α ≤ cofinite := 
  (ultrafilter_of_spec (cofinite_ne_bot hi)).1

lemma is_ultrafilter_hyperfilter (hi : set.infinite (@set.univ α)) : is_ultrafilter (@hyperfilter α) := 
  (ultrafilter_of_spec (cofinite_ne_bot hi)).2

theorem nmem_hyperfilter_of_finite (hi : set.infinite (@set.univ α)) {s : set α} 
: set.finite s → s ∉ (@hyperfilter α).sets :=
  λ hf hy, 
  have hx : -s ∉ hyperfilter.sets := λ hs, 
    (ultrafilter_iff_compl_mem_iff_not_mem.mp (is_ultrafilter_hyperfilter hi) s).mp hs hy,
  have ht : -s ∈ cofinite.sets := by show -s ∈ {s | _}; 
    rwa [set.mem_set_of_eq, lattice.neg_neg],
  hx $ hyperfilter_le_cofinite hi ht

theorem compl_mem_hyperfilter_of_finite (hi : set.infinite (@set.univ α)) {s : set α} 
: set.finite s → -s ∈ (@hyperfilter α).sets :=
  λ hf, (ultrafilter_iff_compl_mem_iff_not_mem.mp 
    (is_ultrafilter_hyperfilter hi) s).mpr $ 
    nmem_hyperfilter_of_finite hi hf

theorem mem_hyperfilter_of_finite_compl (hi : set.infinite (@set.univ α)) {s : set α} 
: set.finite (-s) → s ∈ (@hyperfilter α).sets := 
  λ hf, have h : _ := compl_mem_hyperfilter_of_finite hi hf,
  by rwa [lattice.neg_neg] at h

---

lemma tendsto_at_top_at_bot {α : Type} {β : Type} [nonempty α] [decidable_linear_order α] [preorder β] (f : α → β) : tendsto f at_top at_bot ↔ ∀ (b : β), ∃ (i : α), ∀ (a : α), i ≤ a → b ≥ f a := 
@tendsto_at_top_at_top α (order_dual β) _ _ _ (λ x y, ⟨max x y, ⟨le_max_left _ _, le_max_right _ _⟩⟩) f

end filter

