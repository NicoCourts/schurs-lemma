import algebra.module

class rep (G : Type*) [group G] (𝕜 : Type*) [field 𝕜]
(V : Type*) [add_comm_group V] [has_scalar G V] [vector_space 𝕜 V] :=
(id : ∀ m : V, (1 : G) • m = m)
(action : ∀ g h : G, ∀ m : V, g • (h • m) = (g * h) • m)
(distrib : ∀ g : G, ∀ m n : V, g • (m + n) = g • m + g • n)
(scalar : ∀ k : 𝕜, ∀ v : V, ∀ g : G,  g • (k • v) = k • (g • v))

class subrep (G : Type*) [group G]
(𝕜 : Type*) [field 𝕜]
(V : Type*) [add_comm_group V] [has_scalar G V] [module 𝕜 V] [rep G 𝕜 V] extends submodule 𝕜 V :=
(stable : ∀ g : G, ∀ v : carrier, g • ↑v ∈ carrier)

definition irreducible (G : Type*) [group G]
(𝕜 : Type*) [field 𝕜]
(V : Type*) [add_comm_group V] [has_scalar G V] [module 𝕜 V] [rep G 𝕜 V] :=
(∀ W : subrep G 𝕜 V, /-W = 0 or W = V (but I don't know how to write this)-/)