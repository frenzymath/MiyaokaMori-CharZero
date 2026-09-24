import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0804

/-! # Stalks of a blowup of a local ring over the closed point

Geometric glue for Stacks 0AGR (steps 2 and 5 of the proof of
`AlgebraicGeometry.blowup_regularLocalRing_dimTwo_isRegularLocalRing_stalk`): for a local ring
`A` and an ideal sheaf `I` on `Spec A`, every point `y` of `X = Bl_I Spec A` lying over the closed point
`𝔪` of `Spec A` lies in an affine chart `V_a ≅ Spec A[I/a]` of Stacks 0804
(`AlgebraicGeometry.Scheme.blowup_preimage_affine_cover`, `a ∈ I(Spec A)`), hence corresponds to a
prime `𝔮` of the affine blowup algebra `A[I/a]` with `O_{X,y} ≅ A[I/a]_𝔮`, and `y ↦ 𝔪` translates to
`𝔮 ∩ A = 𝔪` (as ideals of `Γ(Spec A, ⊤) ≅ A`).

Source: Stacks 0804 (charts of a blowup of an affine scheme), 0AGR (proof); used in the proof of
Corollary 4.3 of the paper (§4).
The ring of global sections `Γ(Spec A, ⊤)` is identified with `A` through `Scheme.ΓSpecIso`, so the
maximal ideal appears as `(maximalIdeal A).map (ΓSpecIso A).inv.hom`, exactly as in the statement of
`AlgebraicGeometry.blowup_regularLocalRing_dimTwo_isRegularLocalRing_stalk`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- The point of `Spec Γ(Spec A, ⊤)` corresponding (via `IsAffineOpen.isoSpec` of `⊤`) to the closed
point of `Spec A`, `A` local, is the prime `(maximalIdeal A).map (ΓSpecIso A).inv.hom`: by
`IsAffineOpen.isoSpec_hom_apply` it is the pullback of the maximal ideal of the stalk at the closed
point along the germ map `Γ(Spec A, ⊤) → O_{𝔪}`, which factors as `ΓSpecIso.hom` followed by the
isomorphism `A ≅ O_{𝔪}` (`stalkClosedPointIso`), and isomorphisms of local rings pull the maximal ideal
back to the maximal ideal (`IsLocalRing.comap_closedPoint`). -/
theorem isoSpec_top_hom_closedPoint_asIdeal (A : Type u) [CommRing A] [IsLocalRing A] :
    ((isAffineOpen_top (Spec (CommRingCat.of A))).isoSpec.hom
        ⟨IsLocalRing.closedPoint A, trivial⟩).asIdeal =
      (IsLocalRing.maximalIdeal A).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
  let x₀ : ↑(Spec (CommRingCat.of A)) := IsLocalRing.closedPoint A
  show ((isAffineOpen_top (Spec (CommRingCat.of A))).isoSpec.hom ⟨x₀, trivial⟩).asIdeal = _
  rw [IsAffineOpen.isoSpec_hom_apply]
  change Ideal.comap ((Spec (CommRingCat.of A)).presheaf.germ ⊤ x₀ trivial).hom
    (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of A)).presheaf.stalk x₀)) = _
  have hgerm : (Spec (CommRingCat.of A)).presheaf.germ ⊤ x₀ trivial =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ (stalkClosedPointIso (CommRingCat.of A)).inv :=
    (ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of A)).symm
  rw [hgerm, CommRingCat.hom_comp, ← Ideal.comap_comap]
  have hloc : IsLocalHom (R := A) (S := (Spec (CommRingCat.of A)).presheaf.stalk x₀)
      (stalkClosedPointIso (CommRingCat.of A)).inv.hom :=
    isLocalHom_of_iso (stalkClosedPointIso (CommRingCat.of A)).symm
  have h1 : Ideal.comap (stalkClosedPointIso (CommRingCat.of A)).inv.hom
      (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of A)).presheaf.stalk x₀)) =
        IsLocalRing.maximalIdeal A := by
    have := congrArg PrimeSpectrum.asIdeal
      (IsLocalRing.comap_closedPoint (R := A) (S := (Spec (CommRingCat.of A)).presheaf.stalk x₀)
        (stalkClosedPointIso (CommRingCat.of A)).inv.hom)
    rw [PrimeSpectrum.comap_asIdeal] at this
    exact this
  rw [h1]
  -- `𝔪.comap (ΓSpecIso.hom) = 𝔪.map (ΓSpecIso.inv)` for the ring isomorphism `ΓSpecIso`
  set ε : Γ(Spec (CommRingCat.of A), ⊤) ≃+* A :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv with hε
  ext z
  rw [Ideal.mem_comap, Ideal.mem_map_iff_of_surjective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    ε.symm.surjective]
  constructor
  · intro hz
    exact ⟨_, hz, ε.symm_apply_apply z⟩
  · rintro ⟨w, hw, rfl⟩
    have h : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom w) = w := ε.apply_symm_apply w
    rw [h]
    exact hw

/-- **Charts of a blowup of an affine open, pointwise (Stacks 0804).** `U` an affine open of `X`,
`y` a point of `Bl_I X` over `U`. Then `y` lies in a chart `V_a ≅ Spec A[I(U)/a]`, `a ∈ I(U)`,
`A = Γ(X, U)` (`blowup_preimage_affine_cover`, Stacks 0804); if `p` is the corresponding point
of `Spec A[I(U)/a]`, then `p` maps to the point of `Spec Γ(X, U)` corresponding to `π(y)` under
`U ≅ Spec Γ(X, U)`, and `O_{Bl, y} ≅ A[I(U)/a]_p` (`Spec.stalkIso`, the stalk map of the isomorphism
`V_a ≅ Spec A[I(U)/a]`, and `Scheme.Opens.stalkIso`). -/
theorem Scheme.blowup_exists_chart_point_stalk_equiv {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (y : ↑(Scheme.blowup I).left) (hy : (Scheme.blowup I).hom y ∈ (U : X.Opens)) :
    ∃ (a : I.ideal U) (p : ↑(Spec (CommRingCat.of ((I.ideal U).affineBlowup (a : Γ(X, U)))))),
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) ((I.ideal U).affineBlowup (a : Γ(X, U))))) p =
        U.2.isoSpec.hom ⟨(Scheme.blowup I).hom y, hy⟩ ∧
      Nonempty (@Localization.AtPrime _ _ p.asIdeal p.isPrime ≃+*
        (Scheme.blowup I).left.presheaf.stalk y) := by
  obtain ⟨V, hV, hE, hcov⟩ := Scheme.blowup_preimage_affine_cover I U
  have hycov : y ∈ ⨆ a, V a := by
    rw [hcov]
    exact hy
  obtain ⟨a, hya⟩ := Opens.mem_iSup.mp hycov
  obtain ⟨e, he⟩ := hE a
  refine ⟨a, e.hom ⟨y, hya⟩, ?_, ?_⟩
  · have h1 := congrArg (fun f => f (e.hom ⟨y, hya⟩)) he
    simp only [Scheme.Hom.comp_apply] at h1
    have h2 : e.inv (e.hom ⟨y, hya⟩) = ⟨y, hya⟩ := by
      have := congrArg (fun f => f ⟨y, hya⟩) e.hom_inv_id
      simp only at this
      exact this
    rw [h2, Scheme.homOfLE_apply'] at h1
    have h3 : ((Scheme.blowup I).hom ∣_ (U : X.Opens)) ⟨y, hV a hya⟩ =
        ⟨(Scheme.blowup I).hom y, hy⟩ :=
      Subtype.ext (morphismRestrict_base_coe _ _ _)
    rw [h3] at h1
    exact h1.symm
  · let y' : (V a).toScheme := ⟨y, hya⟩
    haveI := (e.hom y').isPrime
    haveI : IsIso (e.hom.stalkMap y') := inferInstance
    let ε₁ := (Spec.stalkIso (CommRingCat.of ((I.ideal U).affineBlowup (a : Γ(X, U))))
      (e.hom y')).symm.commRingCatIsoToRingEquiv
    let ε₂ := (asIso (e.hom.stalkMap y')).commRingCatIsoToRingEquiv
    let ε₃ := ((V a).stalkIso y').commRingCatIsoToRingEquiv
    exact ⟨(ε₁.trans ε₂).trans ε₃⟩

/-- **Stacks 0AGR, geometric glue.** `A` a local ring, `I` an ideal sheaf on `Spec A`, `y` a point of
`Bl_I Spec A` over the closed point. Then for some `a ∈ I(Spec A)` and some prime `𝔮` of the affine
blowup algebra `A[I/a]` with `𝔮 ∩ A = 𝔪` (the maximal ideal of `A` transported to `Γ(Spec A, ⊤)`), the
local ring `O_{Bl, y}` is isomorphic to `A[I/a]_𝔮`.

Proof. `blowup_preimage_affine_cover` (Stacks 0804) for the affine open `⊤` of
`Spec A` gives opens `V_a` covering `Bl`, isomorphisms `e_a : V_a ≅ Spec A[I/a]` and the compatibility
`e_a.inv ≫ (V_a ↪ Bl) ≫ (π ∣_ ⊤) ≫ isoSpec.hom = Spec.map (algebraMap)`. Pick `a` with `y ∈ V_a` and let
`𝔮` be the prime `e_a(y)`. Evaluating the compatibility at `𝔮` gives `Spec.map (algebraMap) 𝔮 =
isoSpec.hom ⟨π y, _⟩ = isoSpec.hom ⟨𝔪, _⟩`, whose ideal is `𝔪.map (ΓSpecIso A).inv.hom`
(`isoSpec_top_hom_closedPoint_asIdeal`); the left side is `𝔮.comap (algebraMap)`. The stalk isomorphism
is the composite `A[I/a]_𝔮 ≅ O_{Spec A[I/a], 𝔮}` (`Spec.stalkIso`), `≅ O_{V_a, y}` (stalk map of the
isomorphism `e_a`), `≅ O_{Bl, y}` (`Scheme.Opens.stalkIso`, stalks of an open subscheme). -/
theorem Scheme.blowup_spec_stalk_over_closedPoint (A : Type u) [CommRing A] [IsLocalRing A]
    (I : (Spec (CommRingCat.of A)).IdealSheafData) (y : ↑(Scheme.blowup I).left)
    (hy : (Scheme.blowup I).hom y = IsLocalRing.closedPoint A) :
    ∃ (a : I.ideal ⟨⊤, isAffineOpen_top _⟩)
      (𝔮 : Ideal ((I.ideal ⟨⊤, isAffineOpen_top _⟩).affineBlowup
        (a : Γ(Spec (CommRingCat.of A), ⊤))))
      (_ : 𝔮.IsPrime),
      𝔮.comap (algebraMap Γ(Spec (CommRingCat.of A), ⊤)
          ((I.ideal ⟨⊤, isAffineOpen_top _⟩).affineBlowup (a : Γ(Spec (CommRingCat.of A), ⊤)))) =
        (IsLocalRing.maximalIdeal A).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ∧
      Nonempty (Localization.AtPrime 𝔮 ≃+* (Scheme.blowup I).left.presheaf.stalk y) := by
  obtain ⟨a, p, hp, hstalk⟩ := Scheme.blowup_exists_chart_point_stalk_equiv I
    ⟨⊤, isAffineOpen_top _⟩ y trivial
  refine ⟨a, p.asIdeal, p.isPrime, ?_, hstalk⟩
  have hpt : (⟨(Scheme.blowup I).hom y, trivial⟩ : ((⊤ : (Spec (CommRingCat.of A)).Opens) : Type u)) =
      ⟨IsLocalRing.closedPoint A, trivial⟩ := Subtype.ext hy
  have h := congrArg PrimeSpectrum.asIdeal
    (hp.trans (congrArg (isAffineOpen_top (Spec (CommRingCat.of A))).isoSpec.hom hpt))
  exact h.trans (isoSpec_top_hom_closedPoint_asIdeal A)

end AlgebraicGeometry

end
