import representation_hom

variables (G : Type*) [group G] (𝕜 : Type*) [field 𝕜]
variables (V : Type*) [add_comm_group V] [has_scalar G V] [vector_space 𝕜 V]
variables (W : Type*) [add_comm_group W] [has_scalar G W] [vector_space 𝕜 W]

variables [rep G 𝕜 V] [rep G 𝕜 W]

theorem schur1 (irred_V : irreducible G 𝕜 V) (irred_W : irreducible G 𝕜 W) (φ : hom G 𝕜 V W) :
(φ = 0) ∨ ((∀ w, ∃ v, φ v = w) ∧ (∀ v, φ v = 0 → v = 0)) :=
begin
    sorry
end

theorem schur2 (irred_V : irreducible G 𝕜 V) (φ : hom G 𝕜 V V) :
(φ = 0) ∨ (∃ k : 𝕜, φ = k • 1) :=
begin
    sorry
end