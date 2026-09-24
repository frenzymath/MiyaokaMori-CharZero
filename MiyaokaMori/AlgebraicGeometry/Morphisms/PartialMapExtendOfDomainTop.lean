import MiyaokaMori.Prelude

/-! # Extending a partial map whose rational-map domain is everything

A partial map `G` from a reduced scheme to a separated scheme whose rational map class has domain
of definition the whole space extends to a global morphism agreeing with `G` on the domain of `G`
(Debarre, *Introduction to Mori theory*, 5.17, the maximal domain of definition; Hartshorne I
Lemma 4.1 / II Ex. 4.2: morphisms from a reduced scheme to a separated scheme agreeing on a dense
open agree).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.PartialMap.exists_extension_of_domain_eq_top {X Y : Scheme.{u}}
    [IsReduced X] [Y.IsSeparated] (G : X.PartialMap Y) (h : G.toRationalMap.domain = ⊤) :
    ∃ Ψ : X ⟶ Y, G.domain.ι ≫ Ψ = G.hom := by
  let P := G.toRationalMap.toPartialMap
  have hP : P.domain = ⊤ := h
  refine ⟨X.topIso.inv ≫ (X.isoOfEq hP).inv ≫ P.hom, ?_⟩
  have key : X.homOfLE G.le_domain_toRationalMap ≫ P.hom = G.hom :=
    G.toPartialMap_toRationalMap_restrict
  rw [← key, ← Category.assoc, ← Category.assoc]
  congr 1
  refine (cancel_mono (Scheme.Opens.ι P.domain)).mp ?_
  simp only [Category.assoc, Scheme.isoOfEq_inv_ι, Scheme.toIso_inv_ι, Category.comp_id]
  exact (X.homOfLE_ι _).symm

end
