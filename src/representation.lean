import group_theory.submonoid
import algebra.module

variables {G : Type*} [group G]
variables {𝕜 : Type*} [field 𝕜]
variables {M : Type*} [module 𝕜 M]

structure representation (G : Type*) [group G] extends (module 𝕜 M)
