import group_theory.submonoid
import algebra.module

universe u
variables {G : Type u} [group G] {𝕜 : Type u} [field 𝕜] {M : Type u} [add_comm_group M] [module 𝕜 M]

-- From https://github.com/fpvandoorn/group-representations/blob/master/src/group_theory/representation/basic.lean
class G_module (G : Type*) [group G] (M : Type*) [add_comm_group M]
  extends has_scalar G M :=
(id : ∀ m : M, (1 : G) • m = m)
(mul : ∀ g h : G, ∀ m : M, g • (h • m) = (g * h) • m)
(linear : ∀ g : G, ∀ m n : M, g • (m + n) = g • m + g • n)

-- A G-module whose action is 𝕜-linear
structure representation [h: has_scalar 𝕜 M] extends G_module G M :=
(ex : ∀ k : 𝕜, ∀ m : M, ∀ g : G,  g • (k • m) = k • (g • m))
