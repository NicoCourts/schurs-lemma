import representation

variables (G : Type*) [group G] (𝕜 : Type*) [field 𝕜]
variables (V : Type*) [add_comm_group V] [has_scalar G V] [vector_space 𝕜 V]
variables (W : Type*) [add_comm_group W] [has_scalar G W] [vector_space 𝕜 W]

variables [rep G 𝕜 V] [rep G 𝕜 W]

variables (V' : subrep G 𝕜 V) (W' : subrep G 𝕜 W)

class hom :=
(to_fun : V → W)
(equiv : ∀ g : G, ∀ v : V, to_fun (g • v) = g • to_fun v)
(scalar : ∀ k : 𝕜, ∀ v : V, to_fun (k • v) = k • to_fun v)

instance : has_coe_to_fun (hom G 𝕜 V W) := ⟨_, λ m, m.to_fun⟩

--{smul := λ g, λ ⟨v,h⟩, ⟨g • v, V'.stable g ⟨v,h⟩⟩}

instance : semiring (hom G 𝕜 V W) := {
    add := (
        λ ϕ ψ, ⟨(λ v, (ϕ v) + (ψ v)),(begin
            intros g v,
            unfold_coes,
            rw group_module.distrib,
            sorry,
        end)⟩
    ),
    add_assoc := sorry,
    zero := sorry,
    zero_add := sorry,
    add_zero := sorry,
    add_comm := sorry,
    mul := sorry,
    mul_assoc := sorry,
    one := sorry,
    one_mul := sorry,
    mul_one := sorry,
    left_distrib := sorry,
    right_distrib := sorry,
    zero_mul := sorry,
    mul_zero := sorry,
}
instance tada : algebra 𝕜 (hom G 𝕜 V W) := {}

--basic version of schur's lemma
--todo: maybe make separate definitions for isomorphism and for the zero map
--todo: prove this theorem (it might require classical logic?)

theorem irred_thm (irred_V : irreducible G 𝕜 V) (irred_W : irreducible G 𝕜 W) (φ : hom G 𝕜 V W) :
(∀ v, φ v = 0) ∨ ((∀ w, ∃ v, φ v = w) ∧ (∀ v, φ v = 0 → v = 0)) :=
begin
    sorry
end