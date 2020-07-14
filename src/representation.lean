import algebra.module
import linear_algebra.basic
import tactic

variables (G : Type*) [group G] (𝕜 : Type*) [field 𝕜]
variables (V : Type*) [add_comm_group V] [has_scalar G V] [vector_space 𝕜 V]
variables (W : Type*) [add_comm_group W] [has_scalar G W] [vector_space 𝕜 W]

class group_module :=
(id : ∀ v : V, (1 : G) • v = v)
(action : ∀ g h : G, ∀ m : V, g • (h • m) = (g * h) • m)
(distrib : ∀ g : G, ∀ m n : V, g • (m + n) = g • m + g • n)

lemma act_zero [group_module G V] :
∀ g : G, g • (0 : V) = 0 :=
begin
    intro g,
    have h := (group_module.distrib) g (0 : V) (0 : V),
    rw add_zero at h,
    rw add_left_eq_self.1 h.symm,
end

lemma act_neg [group_module G V] :
∀ g : G, ∀ v : V, g • -v = -(g • v) :=
begin
    intros g v,
    have h := (group_module.distrib) g v (-v),
    rw add_right_neg at h,
    rw act_zero at h,
    rw neg_eq_of_add_eq_zero h.symm,
end

class rep extends group_module G V :=
(linear : ∀ k : 𝕜, ∀ v : V, ∀ g : G,  g • (k • v) = k • (g • v))

variables [rep G 𝕜 V] [rep G 𝕜 W]

structure subrep extends submodule 𝕜 V :=
(stable : ∀ g : G, ∀ v : carrier, g • ↑v ∈ carrier)

variables (V' : subrep G 𝕜 V) (W' : subrep G 𝕜 W)

instance : has_coe_t (subrep G 𝕜 V) (set V) := ⟨λ V', V'.carrier⟩
instance : has_mem V (subrep G 𝕜 V) := ⟨λ v V', v ∈ (V' : set V)⟩
instance : has_coe_to_sort (subrep G 𝕜 V) := ⟨_, λ V', {v : V // v ∈ V'}⟩

instance subrep.is_add_comm_group
[h : add_comm_group (V'.to_submodule)] : add_comm_group V' := {.. h}

instance subrep.is_has_scalar : has_scalar G V' :=
{smul := λ g, λ ⟨v,h⟩, ⟨g • v, V'.stable g ⟨v,h⟩⟩}

instance subrep.is_group_module : group_module G V' := {
    id :=
    begin
        intro v,
        cases v,
        change (⟨(1 : G) • _, _⟩ : V') = (⟨v_val, _⟩ : V'),
        rw subtype.mk_eq_mk,
        rw group_module.id,
    end,
    action :=
    begin
        intros g h v,
        cases v,
        change (⟨g • h • _, _⟩ : V') = (⟨(g * h) • _, _⟩ : V'),
        rw subtype.mk_eq_mk,
        rw group_module.action,
    end,
    distrib :=
    begin
        intros g v w,
        cases v,
        cases w,
        change (⟨g • (_ + _), _⟩ : V') = (⟨g • _ + g • _, _⟩ : V'),
        rw subtype.mk_eq_mk,
        rw group_module.distrib,
    end
}

instance subrep.is_vector_space
[h : vector_space 𝕜 (V'.to_submodule)] : vector_space 𝕜 V' := {.. h}

instance subrep.is_rep : rep G 𝕜 V' := {
    linear :=
    begin
        intros k v g,
        cases v,
        change (⟨g • k • _, _⟩ : V') = (⟨k • g • _, _⟩ : V'),
        rw subtype.mk_eq_mk,
        rw rep.linear,
    end
}

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
(∀ V' : subrep G 𝕜 V, (V' = ⊥) ∨ (V' = ⊤))