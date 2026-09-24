import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor

/-! # The Serre twisting sheaf `O(m)` on an absolute Proj

The Serre twisting sheaf `O_{Proj 𝒜}(m)` on the absolute Proj of a graded ring, and the
multiplication maps `O(a) ⊗ O(b) → O(a+b)` (Stacks 01MO). See Lemma 2.2 of the paper for how `O(m)` is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
-- Definitional-equality checks on homogeneous localizations are extremely slow at the default transparency.
set_option backward.isDefEq.respectTransparency false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `O_{Proj 𝒜}(m)`: the sheaf `MiyaokaMori.WeightedJets.ProjTwisting.sheaf`, whose sections are
locally homogeneous fractions of degree `m` (with the convention `S(m)_n = S_{n+m}`), for any
`ℕ`-graded ring and any `m : ℤ`.

This is a `def` rather than an `abbrev`: an `abbrev` would make both the elaborator and the
kernel unfold `Proj.twist` eagerly into `ProjTwisting.sheaf` (a sheafification predicate on
function types over homogeneous localizations), and it would prevent
`attribute [local irreducible] AlgebraicGeometry.Proj.twist`, which downstream modules use to
treat `O(m)` as an opaque object. -/
noncomputable def AlgebraicGeometry.Proj.twist {σ A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (m : ℤ) :
    (AlgebraicGeometry.Proj 𝒜).Modules :=
  MiyaokaMori.WeightedJets.ProjTwisting.sheaf 𝒜 m

/-- `Proj.twist` is `ProjTwisting.sheaf` (definitional equality); use this to unfold it. -/
theorem AlgebraicGeometry.Proj.twist_def {σ A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (m : ℤ) :
    AlgebraicGeometry.Proj.twist 𝒜 m = MiyaokaMori.WeightedJets.ProjTwisting.sheaf 𝒜 m := rfl

/-- The presheaf of sections of `O(m)` is `ProjTwisting.presheaf` (definitional equality). -/
theorem AlgebraicGeometry.Proj.twist_val {σ A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (m : ℤ) :
    (AlgebraicGeometry.Proj.twist 𝒜 m).val = MiyaokaMori.WeightedJets.ProjTwisting.presheaf 𝒜 m := rfl

/- Multiplication of sections `Γ(O(a), U) × Γ(O(b), U) → Γ(O(a+b), U)` on each open set: sections
   are functions with values in homogeneous localizations, multiplied pointwise,
   `(x/s)(y/t) = xy/(st)`; that the product is again locally a fraction of degree `a + b` is the
   proof obligation. -/

open MiyaokaMori.WeightedJets.ProjTwisting in
/-- The product of a homogeneous fraction of degree `a` and one of degree `b` is a homogeneous
fraction of degree `a + b` (multiply numerators and denominators). This is the multiplicative
version of `MiyaokaMori.WeightedJets.ProjTwisting.isFraction_add`. -/
private theorem isFraction_mul {σ A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (a b : ℤ)
    {U : TopologicalSpace.Opens (ProjectiveSpectrum.top 𝒜)}
    {s t : ∀ x : U, Fiber 𝒜 x.1} (hs : IsFraction 𝒜 a s) (ht : IsFraction 𝒜 b t) :
    IsFraction 𝒜 (a + b) (fun x ↦ s x * t x) := by
  rcases hs with rfl | ⟨i, j, p, q, hij, hq, hs⟩
  · exact Or.inl (funext fun x ↦ zero_mul _)
  rcases ht with rfl | ⟨k, l, c, e, hkl, he, ht⟩
  · exact Or.inl (funext fun x ↦ mul_zero _)
  refine Or.inr ⟨i + k, j + l, ⟨p.1 * c.1, SetLike.mul_mem_graded p.2 c.2⟩,
    ⟨q.1 * e.1, SetLike.mul_mem_graded q.2 e.2⟩, by push_cast; omega,
    fun x ↦ x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hq x) (he x), ?_⟩
  intro x
  simp only [hs, ht, Localization.mk_mul]
  rfl

open MiyaokaMori.WeightedJets.ProjTwisting in
/-- The product of a locally-degree-`a` fraction and a locally-degree-`b` fraction is locally a
fraction of degree `a + b` (the multiplicative version of `locallyFraction_add`). -/
private theorem locallyFraction_mul {σ A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (a b : ℤ)
    {U : TopologicalSpace.Opens (ProjectiveSpectrum.top 𝒜)}
    {s t : ∀ x : U, Fiber 𝒜 x.1}
    (hs : (locallyFraction 𝒜 a).pred s) (ht : (locallyFraction 𝒜 b).pred t) :
    (locallyFraction 𝒜 (a + b)).pred (fun x ↦ s x * t x) := by
  apply TopCat.PrelocalPredicate.sheafify_inductionOn₂' (fractionPrelocal 𝒜 a)
    (fractionPrelocal 𝒜 b) (fractionPrelocal 𝒜 (a + b)) (fun u v ↦ u * v) ?_ hs ht
  intro V W p q hp hq
  exact isFraction_mul 𝒜 a b
    ((fractionPrelocal 𝒜 a).res (Opens.infLELeft V W) p hp)
    ((fractionPrelocal 𝒜 b).res (Opens.infLERight V W) q hq)

/-- Pointwise multiplication of sections `Γ(O(a), U) → Γ(O(b), U) → Γ(O(a+b), U)`. -/
noncomputable def AlgebraicGeometry.Proj.twistSectionMul {σ A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (a b : ℤ)
    (U : TopologicalSpace.Opens (ProjectiveSpectrum.top 𝒜)) :
    (MiyaokaMori.WeightedJets.ProjTwisting.presheaf 𝒜 a).obj (Opposite.op U) →
      (MiyaokaMori.WeightedJets.ProjTwisting.presheaf 𝒜 b).obj (Opposite.op U) →
        (MiyaokaMori.WeightedJets.ProjTwisting.presheaf 𝒜 (a + b)).obj (Opposite.op U) :=
  fun s t => ⟨fun x => s.1 x * t.1 x, locallyFraction_mul 𝒜 a b s.2 t.2⟩

/-- The presheaf-level multiplication: on each open set the tensor product
`O(a)(U) ⊗_{O(U)} O(b)(U) → O(a+b)(U)` obtained by `TensorProduct.lift` from the bilinear
multiplication above. The target is written as the image under the right adjoint of the
sheafification adjunction (forget, then `restrictScalars 𝟙`); bilinearity, linearity and
naturality are the proof obligations. -/
noncomputable def AlgebraicGeometry.Proj.twistMulPresheaf {σ A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (a b : ℤ) :
    AlgebraicGeometry.Scheme.Modules.moduleTensorPresheaf (AlgebraicGeometry.Proj.twist 𝒜 a) (AlgebraicGeometry.Proj.twist 𝒜 b) ⟶
      (PresheafOfModules.restrictScalars (𝟙 (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj)).obj
        ((AlgebraicGeometry.Scheme.Modules.toPresheafOfModules _).obj
          (AlgebraicGeometry.Proj.twist 𝒜 (a + b))) where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (R := (((AlgebraicGeometry.Proj 𝒜).presheaf ⋙ CategoryTheory.forget₂ CommRingCat RingCat).obj U : RingCat))
    (M₃ := ((PresheafOfModules.restrictScalars (𝟙 (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj)).obj
        ((AlgebraicGeometry.Scheme.Modules.toPresheafOfModules _).obj
          (AlgebraicGeometry.Proj.twist 𝒜 (a + b)))).obj U)
    (AlgebraicGeometry.Proj.twistSectionMul 𝒜 a b U.unop)
    (fun s s' t ↦ Subtype.ext (funext fun x ↦ add_mul _ _ _))
    (fun r s t ↦ Subtype.ext (funext fun x ↦ mul_assoc _ _ _))
    (fun s t t' ↦ Subtype.ext (funext fun x ↦ mul_add _ _ _))
    (fun r s t ↦ Subtype.ext (funext fun x ↦ mul_left_comm _ _ _))
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s t
    rfl

/-- The multiplication `O(a) ⊗ O(b) → O(a+b)` (Stacks 01MO): `Modules.tensor` is the
sheafification of the presheaf of open-set-wise tensor products (`AlgebraicGeometry.Scheme.Modules.moduleTensor`), and
the presheaf morphism above is lifted through the sheafification adjunction. -/
noncomputable def AlgebraicGeometry.Proj.twistMul {σ A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (a b : ℤ) :
    AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Proj.twist 𝒜 a) (AlgebraicGeometry.Proj.twist 𝒜 b) ⟶
      AlgebraicGeometry.Proj.twist 𝒜 (a + b) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj)).homEquiv
    _ _).symm (AlgebraicGeometry.Proj.twistMulPresheaf 𝒜 a b)

end
