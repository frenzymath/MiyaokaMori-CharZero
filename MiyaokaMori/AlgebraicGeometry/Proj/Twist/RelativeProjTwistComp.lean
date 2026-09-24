import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwist

/-! # Transitivity of the transition maps of the relative twisting sheaf

Statement: transitivity of the transition maps `twistTransition` of `RelativeProjTwist`
(for `U ≤ V ≤ W`, `θ_{W→U} = θ_{W→V} ≫ θ_{V→U}`), i.e. the `map_comp` field of `twistDiagram`.

Compile-time remark: this theorem once took the kernel 37–43 s. The proof term is a single lemma application; the
cost was that the statement is spelled with `S.twistTransition …` while the instance of `Proj.twistPushTransition_comp`
is spelled with `Proj.twistPushTransition …`. The two differ by one delta step, and on the right-hand side the
difference sits below `CategoryStruct.comp` (a head whose reducibility hints are those of an `abbrev`): for an `abbrev`
head the kernel does not compare the arguments first but unfolds both `comp`s together with the concrete morphisms
inside. The generic bridge lemmas below fix this: the three morphisms enter as "variables + top-level `HEq.rfl`", the
conclusion of the lemma instance is **syntactically** the statement, and the delta step is discharged at the top level
(`twistTransition` is a plain `def`, so the kernel compares arguments first). Kernel time went from 37 s to
milliseconds.

**A pitfall when using the bridge lemmas**: the primed morphisms `f' g' k'` are **explicit** arguments and must be
written exactly as in the statement; do not wrap the bridge application in `.symm` — dot notation makes Lean elaborate
the bridge application without an expected type, `HEq.rfl : HEq ?f' f` assigns `?f'` the spelling of the lemma side,
the conclusion falls back to the lemma's spelling, and the slow check returns (43 s). For the other direction use
`eq_comp_of_heq_bridge`.

Sources: Stacks 01LI, 01NP.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace CategoryTheory

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- Bridge lemma (at the level of variables): `f ≫ g = k` respelled as `f' ≫ g' = k'`. Objects and morphisms are
variables; the concrete level discharges the equality of the two spellings by a top-level `rfl` / `HEq.rfl`.
`f' g' k'` are explicit and are written by the caller in the spelling of the **statement**. -/
theorem comp_eq_of_heq_bridge {A B D A' B' D' : C} {f : A ⟶ B} {g : B ⟶ D} {k : A ⟶ D}
    (h : f ≫ g = k) (f' : A' ⟶ B') (g' : B' ⟶ D') (k' : A' ⟶ D')
    (hA : A' = A) (hB : B' = B) (hD : D' = D)
    (hf : HEq f' f) (hg : HEq g' g) (hk : HEq k' k) : f' ≫ g' = k' := by
  subst hA; subst hB; subst hD
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hk
  exact h

/-- The other direction of `comp_eq_of_heq_bridge`: `k = f ≫ g` respelled as `k' = f' ≫ g'`. -/
theorem eq_comp_of_heq_bridge {A B D A' B' D' : C} {f : A ⟶ B} {g : B ⟶ D} {k : A ⟶ D}
    (h : k = f ≫ g) (f' : A' ⟶ B') (g' : B' ⟶ D') (k' : A' ⟶ D')
    (hA : A' = A) (hB : B' = B) (hD : D' = D)
    (hf : HEq f' f) (hg : HEq g' g) (hk : HEq k' k) : k' = f' ≫ g' :=
  (comp_eq_of_heq_bridge h.symm f' g' k' hA hB hD hf hg hk).symm

/-- Bridge lemma (at the level of variables): `f = 𝟙 A` respelled as `f' = 𝟙 A'`. -/
theorem eq_id_of_heq_bridge {A A' : C} {f : A ⟶ A} (h : f = 𝟙 A) (f' : A' ⟶ A')
    (hA : A' = A) (hf : HEq f' f) : f' = 𝟙 A' := by
  subst hA
  obtain rfl := eq_of_heq hf
  exact h

end CategoryTheory

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra

variable {X : Scheme.{u}} (S : X.GradedAffineAlgebra)

theorem twistTransition_comp (m : ℤ) {U V W : X.AffineZariskiSite} (hUV : U ≤ V) (hVW : V ≤ W) :
    S.twistTransition m (hUV.trans hVW) = S.twistTransition m hVW ≫ S.twistTransition m hUV :=
  eq_comp_of_heq_bridge
    (Proj.twistPushTransition_comp (S.restrictGraded hVW) (S.restrictGraded hUV)
      (S.restrictGraded (hUV.trans hVW)) (S.restrict_irrelevant_le hVW) (S.restrict_irrelevant_le hUV)
      (S.restrict_irrelevant_le (hUV.trans hVW)) m
      (congrArg (fun f : S.grading W →+*ᵍ S.grading U =>
        (f : S.toAffineAlgebra.sections W →+* S.toAffineAlgebra.sections U))
        (S.restrictGraded_trans hUV hVW))
      (S.projChart W) (S.projChart V) (S.projChart U)
      (S.map_projChart hVW) (S.map_projChart hUV) (S.map_projChart (hUV.trans hVW)))
    (S.twistTransition m hVW) (S.twistTransition m hUV) (S.twistTransition m (hUV.trans hVW))
    rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl

end AlgebraicGeometry.Scheme.GradedAffineAlgebra

end
