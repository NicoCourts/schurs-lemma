import isomorphism

variables (G : Type*) [group G] (𝕜 : Type*) [field 𝕜]
variables (V : Type*) [add_comm_group V] [has_scalar G V] [vector_space 𝕜 V]
variables (W : Type*) [add_comm_group W] [has_scalar G W] [vector_space 𝕜 W]

variables [rep G 𝕜 V] [rep G 𝕜 W]

theorem schur1 (irred_V : irreducible G 𝕜 V) (irred_W : irreducible G 𝕜 W) (φ : hom G 𝕜 V W) :
(φ = 0) ∨ (iso G 𝕜 V W φ) :=
begin
    cases irred_V (ker G 𝕜 V W φ) with hV hV,
    cases irred_W (im G 𝕜 V W φ) with hW hW,
    left,
    exact im_trivial_implies_zero G 𝕜 V W φ hW,
    right,
    exact ⟨ker_trivial_implies_mono G 𝕜 V W φ hV,im_all_implies_epi G 𝕜 V W φ hW⟩,
    left,
    exact ker_all_implies_zero G 𝕜 V W φ hV,
end

theorem schur2 (irred_V : irreducible G 𝕜 V) (φ : hom G 𝕜 V V) :
(φ = 0) ∨ (∃ k : 𝕜, φ = k • 1) :=
begin
    sorry
end