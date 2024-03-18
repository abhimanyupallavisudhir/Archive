import algebra.group
import data.set.basic

class has_act (G : Type*) (X : Type*) := (act : G → X → X)
class transformation_space (G : Type*) (X : Type*) [group G] extends has_act G X :=
(one_act (x : X) : act 1 x = x)
(act_compat (g h : G) (x : X) : act (g * h) x = act g (act h x))
notation g `⬝` x := has_act.act g x

variables {G : Type*} {X : Type*} [group G] [transformation_space G X]

@[simp] lemma one_act {x : X} : (1 : G) ⬝ x = x := transformation_space.one_act _ _
@[simp] lemma act_compat {g h : G} {x : X} : (g * h) ⬝ x = g ⬝ (h ⬝ x) := transformation_space.act_compat _ _ _

lemma inv_act {g : G} {x y : X} : g ⬝ x = y → g⁻¹ ⬝ y = x :=
λ hxy, by rw [←@one_act G _ _ _ x, ←inv_mul_self g, act_compat, hxy]

lemma inv_act_iff {g : G} {x y : X} : g ⬝ x = y ↔ g⁻¹ ⬝ y = x :=
⟨inv_act, by rw [←inv_inv g] {occs := occurrences.pos [2]}; apply inv_act⟩

lemma permutation_injective {g : G} {x y : X} : g ⬝ x = g ⬝ y → x = y :=
λ hxy, have hxy' : _ := (inv_act hxy).symm, 
by rwa [←act_compat, inv_mul_self, one_act] at hxy'

lemma eq_iff_act_eq {g : G} {x y : X} : x = y ↔ g ⬝ x = g ⬝ y :=
⟨λ hxy, by rw hxy, permutation_injective⟩ 

theorem permutation_bijective (g : G) : function.bijective (λ x : X, g ⬝ x) :=
⟨λ x y, permutation_injective, 
 λ y, ⟨g⁻¹ ⬝ y, by simp [act_compat.symm]⟩⟩

def orbit (x : X) := {y : X | ∃ g : G, g ⬝ x = y}
def in_orbit (x y : X) := (@orbit G _ _ _ x) y

lemma in_orbit_iff_orbit_eq (x y : X) 
: (@in_orbit G X _ _ x y) ↔ (@orbit G _ _ _ x) = (@orbit G _ _ _ y) :=
⟨λ ⟨g, hxy⟩, set.ext (λ z,
  ⟨λ ⟨h, hxz⟩, ⟨h * g⁻¹, by rwa [←hxz, act_compat, ←eq_iff_act_eq, ←inv_act_iff]⟩,
   λ ⟨h, hyz⟩, ⟨h * g, by rwa [act_compat, hxy]⟩⟩),
 (λ hxy, (set.subset.antisymm_iff.mp hxy).2 ⟨1, one_act⟩)⟩

theorem in_orbit_equivalence : equivalence (@in_orbit G X _ _) :=
⟨λ x, ⟨1, one_act⟩,
 λ x y ⟨g, hxy⟩, ⟨g⁻¹, by rw [eq_comm, ←@one_act G _ _ _ x, ←inv_mul_self g, act_compat, hxy]⟩,
 λ x y z ⟨g, hxy⟩ ⟨h, hyz⟩, ⟨h * g, by rwa [act_compat, hxy]⟩⟩ 

def stabiliser (x : X) := {g : G | g ⬝ x = x}
