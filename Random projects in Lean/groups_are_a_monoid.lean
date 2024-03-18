import group_theory

-- Live WebAssembly version of Lean
#eval let v := lean.version in let s := lean.special_version_desc in string.join
["Lean (version ", v.1.repr, ".", v.2.1.repr, ".", v.2.2.repr, ", ",
if s ≠ "" then s ++ ", " else s, "commit ", (lean.githash.to_list.take 12).as_string, ")"]

open classical

def groups := {S : Type // nonempty (group S)}

instance : monoid groups := 
{  mul := λ G H, ⟨ G.val × H.val, nonempty.intro $ 
     { mul := λ gh1 gh2, 
         have hG : group G.val := some (exists_true_of_nonempty G.property),
         have hH : group H.val := some (exists_true_of_nonempty H.property),
         (@group.mul _ hG gh1.1 gh2.1, @group.mul _ hH gh1.2 gh2.2),
       mul_assoc := sorry,
       one := sorry,
       one_mul := sorry,
       mul_one := sorry,
       inv := sorry,
       mul_left_inv := sorry,
     }
     ⟩,
   mul_assoc := sorry,
   one := sorry,
   one_mul := sorry,
   mul_one := sorry,
}

#check @group.mul