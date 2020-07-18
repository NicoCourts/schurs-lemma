import representation_hom

variables (G : Type*) [group G] (𝕜 : Type*) [field 𝕜]
variables (V : Type*) [add_comm_group V] [has_scalar G V] [vector_space 𝕜 V]
variables (W : Type*) [add_comm_group W] [has_scalar G W] [vector_space 𝕜 W]

variables [rep G 𝕜 V] [rep G 𝕜 W]

definition mono (φ : hom G 𝕜 V W) := ∀ v : V, φ v = 0 → v = 0

definition epi (φ : hom G 𝕜 V W) := ∀ w : W, ∃ v : V, φ v = w

definition iso (φ : hom G 𝕜 V W) := (mono G 𝕜 V W φ) ∧ (epi G 𝕜 V W φ)

definition to_module_hom (φ : hom G 𝕜 V W) : (V →ₗ[𝕜] W) := {
    to_fun := φ.to_fun,
    map_add' := φ.add',
    map_smul' := φ.scalar'
}

definition ker (φ : hom G 𝕜 V W) : subrep G 𝕜 V :=
⟨(to_module_hom G 𝕜 V W φ).ker,
begin
    intros g v,
    cases v with v hv,
    change φ v = 0 at hv,
    change φ (g • v) = 0,
    rw[equivariant,hv,act_zero],
end⟩

definition im (φ : hom G 𝕜 V W) : subrep G 𝕜 W :=
⟨(to_module_hom G 𝕜 V W φ).range,
begin
    intros g w,
    cases w with w hw,
    change ∃ v : V, v ∈ (⊤ : set V) ∧ φ v = w at hw,
    change ∃ v : V, v ∈ (⊤ : set V) ∧ φ v = g • w,
    cases hw with v hv,
    use g • v,
    rw[equivariant,hv.2],
    exact ⟨trivial,rfl⟩,
end⟩

lemma ker_trivial_implies_mono (φ : hom G 𝕜 V W) : ker G 𝕜 V W φ = ⊥ → mono G 𝕜 V W φ :=
begin
    intros hφ v hv,
    change v ∈ ker G 𝕜 V W φ at hv,
    rw hφ at hv,
    exact hv,
end

lemma ker_all_implies_zero (φ : hom G 𝕜 V W) : ker G 𝕜 V W φ = ⊤ → φ = 0 :=
begin
    intro hφ,
    rw ext_iff,
    intro v,
    change v ∈ ker G 𝕜 V W φ,
    rw hφ,
    exact trivial,
end

lemma im_trivial_implies_zero (φ : hom G 𝕜 V W) : im G 𝕜 V W φ = ⊥ → φ = 0 :=
begin
    intro hφ,
    rw ext_iff,
    intro v,
    have hv : φ v ∈ im G 𝕜 V W φ,
    exact ⟨v,⟨trivial,by refl⟩⟩,
    rw hφ at hv,
    exact hv,
end

lemma im_all_implies_epi (φ : hom G 𝕜 V W) : im G 𝕜 V W φ = ⊤ → epi G 𝕜 V W φ :=
begin
    intros hφ w,
    have hw : w ∈ (⊤ : subrep G 𝕜 W),
    exact trivial,
    rw ←hφ at hw,
    cases hw with w hw,
    exact ⟨w,hw.2⟩,
end