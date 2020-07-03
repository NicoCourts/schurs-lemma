import algebra.module
import linear_algebra.basic
import tactic

variables (G : Type*) [group G] (𝕜 : Type*) [field 𝕜]
variables (V : Type*) [add_comm_group V] [has_scalar G V] [vector_space 𝕜 V]
variables (W : Type*) [add_comm_group W] [has_scalar G W] [vector_space 𝕜 W]

class group_module :=
(id : ∀ m : V, (1 : G) • m = m)
(action : ∀ g h : G, ∀ m : V, g • (h • m) = (g * h) • m)
(distrib : ∀ g : G, ∀ m n : V, g • (m + n) = g • m + g • n)

lemma act_zero [group_module G V] :
∀ g : G, g • (0 : V) = 0 :=
begin
    intro g,
    have h := (group_module.distrib) g (0 : V) (0 : V),
    rw add_zero at h,
    exact add_left_eq_self.1 (eq.symm h),
end

class rep extends group_module G V :=
(linear : ∀ k : 𝕜, ∀ v : V, ∀ g : G,  g • (k • v) = k • (g • v))

variables [rep G 𝕜 V] [rep G 𝕜 W]

class subrep extends submodule 𝕜 V :=
(stable : ∀ g : G, ∀ v : carrier, g • ↑v ∈ carrier)

lemma bot_closed :
∀ g : G, ∀ (v : (⊥ : submodule 𝕜 V)), g • ↑v ∈ (⊥ : submodule 𝕜 V) :=
begin
    intros g v,
    rw submodule.mem_bot,
    rw (submodule.mem_bot 𝕜).1 (submodule.coe_mem v),
    exact act_zero G V g,
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

instance : has_coe_to_fun (hom G 𝕜 V W) := ⟨_, λ m, m.to_fun⟩

--basic version of schur's lemma
--todo: maybe make separate definitions for isomorphism and for the zero map
--todo: prove this theorem (it might require classical logic?)

theorem irred_thm (irred_V : irreducible G 𝕜 V) (irred_W : irreducible G 𝕜 W) (φ : hom G 𝕜 V W) :
(∀ v, φ v = 0) ∨ ((∀ w, ∃ v, φ v = w) ∧ (∀ v, φ v = 0 → v = 0)) :=
begin
    sorry
end