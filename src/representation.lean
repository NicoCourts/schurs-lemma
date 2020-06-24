import algebra.module
import linear_algebra.basic

class rep (G : Type*) [group G] (𝕜 : Type*) [field 𝕜]
(V : Type*) [add_comm_group V] [has_scalar G V] [vector_space 𝕜 V] :=
(id : ∀ m : V, (1 : G) • m = m)
(action : ∀ g h : G, ∀ m : V, g • (h • m) = (g * h) • m)
(distrib : ∀ g : G, ∀ m n : V, g • (m + n) = g • m + g • n)
(scalar : ∀ k : 𝕜, ∀ v : V, ∀ g : G,  g • (k • v) = k • (g • v))

variables (G : Type*) [group G] (𝕜 : Type*) [field 𝕜] (V : Type*) [add_comm_group V] [has_scalar G V] [module 𝕜 V] [rep G 𝕜 V]

class subrep extends submodule 𝕜 V :=
(stable : ∀ g : G, ∀ v : carrier, g • ↑v ∈ carrier)

lemma lem1 (G : Type*) [group G]
(𝕜 : Type*) [field 𝕜]
(V : Type*) [add_comm_group V] [has_scalar G V] [module 𝕜 V] [rep G 𝕜 V] :
∀ (g : G), ∀ (v : ((⊥ : submodule 𝕜 V).carrier)), g • ↑v ∈ (⊥ : submodule 𝕜 V).carrier :=
begin
    intros g h,
    --rw submodule.mem_bot,
    sorry
end

instance : has_bot (subrep G 𝕜 V) :=
begin
    use ⊥,
    exact lem1 G 𝕜 V,
end

instance : has_top (subrep G 𝕜 V) :=
begin
    use ⊤,
    sorry
end

definition irreducible (G : Type*) [group G]
(𝕜 : Type*) [field 𝕜]
(V : Type*) [add_comm_group V] [has_scalar G V] [module 𝕜 V] [rep G 𝕜 V] :=
(∀ W : subrep G 𝕜 V, (W = ⊥) ∨ (W = ⊤))