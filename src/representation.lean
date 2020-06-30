import algebra.module
import linear_algebra.basic
import tactic

variables (G : Type*) [group G] (𝕜 : Type*) [field 𝕜]
variables (V : Type*) [add_comm_group V] [has_scalar G V] [vector_space 𝕜 V]
variables (W : Type*) [add_comm_group W] [has_scalar G W] [vector_space 𝕜 W]

class rep :=
(id : ∀ m : V, (1 : G) • m = m)
(action : ∀ g h : G, ∀ m : V, g • (h • m) = (g * h) • m)
(distrib : ∀ g : G, ∀ m n : V, g • (m + n) = g • m + g • n)
(scalar : ∀ k : 𝕜, ∀ v : V, ∀ g : G,  g • (k • v) = k • (g • v))

variables [rep G 𝕜 V] [rep G 𝕜 W]

class subrep extends submodule 𝕜 V :=
(stable : ∀ g : G, ∀ v : carrier, g • ↑v ∈ carrier)

--weird thing: I specifically have to tell this lemma that [rep G 𝕜 V], even though it's already in variables
lemma act_zero [h : rep G 𝕜 V] :
∀ g : G, g • (0 : V) = 0 :=
begin
    intro g,
    have h := h.distrib,
    specialize h g (0 : V) (0 : V),
    rw add_zero at h,
    exact add_left_eq_self.1 (eq.symm h),
end

lemma bot_closed :
∀ g : G, ∀ (v : (⊥ : submodule 𝕜 V)), g • ↑v ∈ (⊥ : submodule 𝕜 V) :=
begin
    intros g v,
    rw submodule.mem_bot,
    rw (submodule.mem_bot 𝕜).1 (submodule.coe_mem v),
    exact act_zero G 𝕜 V g,
end

lemma top_closed :
∀ g : G, ∀ (v : (⊤ : submodule 𝕜 V)), g • ↑v ∈ (⊤ : submodule 𝕜 V) :=
begin
    intros g v,
    exact trivial,
end

instance : has_bot (subrep G 𝕜 V) := ⟨⟨⊥,bot_closed G 𝕜 V⟩⟩

instance : has_top (subrep G 𝕜 V) := ⟨⟨⊤,top_closed G 𝕜 V⟩⟩

definition irreducible : Prop :=
(∀ V₀ : subrep G 𝕜 V, (V₀ = ⊥) ∨ (V₀ = ⊤))

--here's an attempt at defining a hom

class hom :=
(to_fun : V → W)
(equiv : ∀ g : G, ∀ v : V, to_fun (g • v) = g • to_fun v)
(scalar : ∀ k : 𝕜, ∀ v : V, to_fun (k • v) = k • to_fun v)

variables (phi : hom G 𝕜 V W)

--having trouble with this

theorem schur (irred_V : irreducible G 𝕜 V) (irred_W : irreducible G 𝕜 W) :
∃ k : 𝕜, ∀ v : V, phi.to_fun (k • v) = k • (phi.to_fun v) :=