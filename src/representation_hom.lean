import representation
import ring_theory.algebra
import algebra.module

variables (G : Type*) [group G] (𝕜 : Type*) [field 𝕜]
variables (V : Type*) [add_comm_group V] [has_scalar G V] [vector_space 𝕜 V]
variables (W : Type*) [add_comm_group W] [has_scalar G W] [vector_space 𝕜 W]

variables [rep G 𝕜 V] [rep G 𝕜 W]

variables (V' : subrep G 𝕜 V) (W' : subrep G 𝕜 W)

structure hom :=
(to_fun : V → W)
(equiv : ∀ g : G, ∀ v : V, to_fun (g • v) = g • to_fun v)
(scalar : ∀ k : 𝕜, ∀ v : V, to_fun (k • v) = k • to_fun v)

instance : has_coe_to_fun (hom G 𝕜 V W) := ⟨_, λ m, m.to_fun⟩

lemma to_fun_eq_coe (φ : hom G 𝕜 V W) : φ.to_fun = φ := rfl

instance : semiring (hom G 𝕜 V W) := {
    add := λ φ ψ, ⟨λ v, (φ v) + (ψ v),
    begin
        intros g v,
        rw group_module.distrib,
        rw ←to_fun_eq_coe,
        rw hom.equiv,
        rw ←to_fun_eq_coe,
        rw hom.equiv,
    end,
    begin
        intros k v,
        rw smul_add,
        rw ←to_fun_eq_coe,
        rw hom.scalar,
        rw ←to_fun_eq_coe,
        rw hom.scalar,
    end⟩,
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
instance : algebra 𝕜 (hom G 𝕜 V W) := {
    to_fun := sorry,
    map_one' := sorry,
    map_mul' := sorry,
    map_zero' := sorry,
    map_add' := sorry,
    commutes' := sorry,
    smul_def' := sorry
}

--basic version of schur's lemma
--todo: maybe make separate definitions for isomorphism and for the zero map
--todo: prove this theorem (it might require classical logic?)

theorem irred_thm (irred_V : irreducible G 𝕜 V) (irred_W : irreducible G 𝕜 W) (φ : hom G 𝕜 V W) :
(∀ v, φ v = 0) ∨ ((∀ w, ∃ v, φ v = w) ∧ (∀ v, φ v = 0 → v = 0)) :=
begin
    sorry
end