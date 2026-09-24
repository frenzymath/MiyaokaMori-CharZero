import MiyaokaMori.AlgebraicGeometry.Blowup.SurfaceBlowup

/-!
# A scheme-theoretic closure model for strict transform

For the same centre ideal `I` and maps `b : B ⟶ X`, `j : C ⟶ X`, form
`C ×[X] B`. Remove the support of the pullback of `I` to this fibre product,
and take the scheme-theoretic image of the resulting open immersion. This
defines a closed subscheme using the actual kernel ideal, without replacing
that ideal by its radical or imposing reducedness or integrality.

If this open immersion is quasi-compact, the kernel ideal on every affine open
is exactly the kernel of the open restriction map, and its support is the
topological closure of the open. A locally Noetherian fibre product supplies
the needed quasi-compactness through Mathlib's open-immersion instance.

This is only a closure MODEL for the strict transform in Stacks Tags 080D and
080E (`divisors.tex`, Section Strict transform). Identifying it with the
supported-sections torsion quotient, identifying the resulting blowup, proving
the curve projection is an isomorphism, and computing the exceptional
intersection and its length remain separate obligations. No blowup property
or such identification is assumed in this construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Blowup.StrictTransformClosureModel

universe u

variable {X B C : Scheme.{u}} (I : X.IdealSheafData) (b : B ⟶ X) (j : C ⟶ X)

/-- The actual pullback of the specified centre ideal to the fibre product. -/
def exceptionalIdeal : (pullback j b).IdealSheafData :=
  (I.comap b).comap (pullback.snd j b)

/-- The open complement of the exceptional ideal's support in the fibre product. -/
def away : (pullback j b).Opens :=
  (exceptionalIdeal I b j).support.compl

/-- The kernel ideal defining the scheme-theoretic closure model. -/
def closureIdeal : (pullback j b).IdealSheafData :=
  (away I b j).ι.ker

/-- The strict-transform closure model, with its full scheme structure. -/
def model : Scheme.{u} :=
  (closureIdeal I b j).subscheme

/-- The canonical closed inclusion of the closure model into the fibre product. -/
def ι : model I b j ⟶ pullback j b :=
  (closureIdeal I b j).subschemeι

/-- The closure model's actual projection to the original scheme `C`. -/
def q : model I b j ⟶ C :=
  ι I b j ≫ pullback.fst j b

/-- The closure model's actual map to the modified ambient scheme `B`. -/
def i : model I b j ⟶ B :=
  ι I b j ≫ pullback.snd j b

/-- The canonical factorization of the centre-free open through the closure model. -/
def openToModel : (away I b j).toScheme ⟶ model I b j :=
  (away I b j).ι.toImage

/-- The model is a closed subscheme of the same fibre product. -/
instance isClosedImmersion_ι : IsClosedImmersion (ι I b j) := by
  exact inferInstanceAs (IsClosedImmersion (closureIdeal I b j).subschemeι)

/-- For a closed original immersion, the model is a closed subscheme of `B`. -/
instance isClosedImmersion_i [IsClosedImmersion j] : IsClosedImmersion (i I b j) := by
  dsimp [i]
  infer_instance

/-- The two structural maps retain the original cartesian compatibility. -/
theorem i_comp_b : i I b j ≫ b = q I b j ≫ j := by
  simp only [i, q, Category.assoc, pullback.condition]

/-- The open-to-model map factors the original open immersion, as scheme morphisms. -/
@[reassoc (attr := simp)]
theorem openToModel_ι : openToModel I b j ≫ ι I b j = (away I b j).ι :=
  (away I b j).ι.toImage_imageι

-- For a blowup application, deriving this quasi-compactness from the locally
-- principal exceptional ideal in `IsBlowup` is a separate construction task.

/-- Under quasi-compactness, the closure ideal has the topological closure as support. -/
theorem support_closureIdeal [QuasiCompact (away I b j).ι] :
    ((closureIdeal I b j).support : Set ↑(pullback j b)) =
      closure (away I b j : Set ↑(pullback j b)) := by
  rw [closureIdeal, Scheme.Hom.support_ker, Scheme.Opens.range_ι]

/-- The image of the model's inclusion is the closure of the centre-free open. -/
theorem range_ι [QuasiCompact (away I b j).ι] :
    Set.range (ι I b j) = closure (away I b j : Set ↑(pullback j b)) := by
  exact (Scheme.IdealSheafData.range_subschemeι (closureIdeal I b j)).trans
    (support_closureIdeal I b j)

/-- On each affine open, the defining ideal is the actual open restriction kernel.
The quasi-compactness hypothesis ensures this component-wise kernel is quasi-coherent. -/
theorem closureIdeal_apply [QuasiCompact (away I b j).ι]
    (V : (pullback j b).affineOpens) :
    (closureIdeal I b j).ideal V = RingHom.ker ((away I b j).ι.app V).hom :=
  Scheme.Hom.ker_apply (away I b j).ι V

/-- The same affine ideal written directly with the ambient structure-sheaf restriction.
The target open is the part of `V` lying in the centre-free open, not its reduction. -/
theorem closureIdeal_apply_restriction [QuasiCompact (away I b j).ι]
    (V : (pullback j b).affineOpens) :
    (closureIdeal I b j).ideal V =
      RingHom.ker ((pullback j b).presheaf.map
        (homOfLE (x := (away I b j).ι ''ᵁ (away I b j).ι ⁻¹ᵁ V)
          (Set.image_preimage_subset _ _)).op).hom := by
  rw [closureIdeal_apply, Scheme.Opens.ι_app]
  rfl

/-- Sections on the model above an affine open are the quotient by its actual ideal.
Together with `closureIdeal_apply`, this records the scheme structure beyond its support. -/
def affineSectionsIso (V : (pullback j b).affineOpens) :
    Γ(model I b j, ι I b j ⁻¹ᵁ V) ≅
      CommRingCat.of (Γ(pullback j b, V) ⧸ (closureIdeal I b j).ideal V) :=
  (closureIdeal I b j).subschemeObjIso V

end AlgebraicGeometry.Blowup.StrictTransformClosureModel
