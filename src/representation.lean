import algebra.module
import linear_algebra.basic
import tactic

class rep (G : Type*) [group G] (𝕜 : Type*) [field 𝕜]
(V : Type*) [add_comm_group V] [has_scalar G V] [vector_space 𝕜 V] :=
(id : ∀ m : V, (1 : G) • m = m)
(action : ∀ g h : G, ∀ m : V, g • (h • m) = (g * h) • m)
(distrib : ∀ g : G, ∀ m n : V, g • (m + n) = g • m + g • n)
(scalar : ∀ k : 𝕜, ∀ v : V, ∀ g : G,  g • (k • v) = k • (g • v))

variables (G : Type*) [group G] (𝕜 : Type*) [field 𝕜] (V : Type*) [add_comm_group V] [has_scalar G V] [module 𝕜 V] [rep G 𝕜 V]

class subrep extends submodule 𝕜 V :=
(stable : ∀ g : G, ∀ v : carrier, g • ↑v ∈ carrier)

lemma act_zero (G : Type*) [group G]
(𝕜 : Type*) [field 𝕜]
(V : Type*) [add_comm_group V] [has_scalar G V] [module 𝕜 V] [h : rep G 𝕜 V] :
∀ g : G, g • (0 : V) = 0 :=
begin
    intro g,
    have hyp := h.distrib,
    specialize hyp g (0 : V) (0 : V),
    rw add_zero at hyp,
    by {exact add_left_eq_self.mp (congr_arg (has_add.add (g • 0)) (congr_arg (has_add.add (g • 0)) (eq.symm hyp)))},
end

lemma lem1 (G : Type*) [group G]
(𝕜 : Type*) [field 𝕜]
(V : Type*) [add_comm_group V] [has_scalar G V] [module 𝕜 V] [rep G 𝕜 V] :
∀ g : G, ∀ (v : (⊥ : submodule 𝕜 V)), g • ↑v ∈ (⊥ : submodule 𝕜 V) :=
begin
    intros g v,
    rw submodule.mem_bot,
    have h := submodule.coe_mem v,
    rw submodule.mem_bot at h,
    rw h,
    exact act_zero G 𝕜 V g,
end

instance : has_bot (subrep G 𝕜 V) :=
begin
    use ⊥,
    exact lem1 G 𝕜 V,
end

instance : has_top (subrep G 𝕜 V) :=
begin
    use ⊤,
    intros g v,
    exact dec_trivial,
end

definition irreducible (G : Type*) [group G]
(𝕜 : Type*) [field 𝕜]
(V : Type*) [add_comm_group V] [has_scalar G V] [module 𝕜 V] [rep G 𝕜 V] :=
(∀ W : subrep G 𝕜 V, (W = ⊥) ∨ (W = ⊤))