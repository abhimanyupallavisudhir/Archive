open function

variables (f : ℤ → ℤ) (hf : ∀ x : ℤ, f(f(x)) = x + 2019)

include hf

lemma bij_f : bijective f :=
⟨ λ x y h, @eq_of_add_eq_add_right _ _ x (2019 : ℤ) y (by rw [←hf, ←hf, h]), 
  λ y, ⟨ f(y - 2019), 
    have hf' : _ := hf (y - 2019), by rwa sub_add_cancel at hf'⟩ ⟩ 

def

theorem p3 : false :=
begin

end