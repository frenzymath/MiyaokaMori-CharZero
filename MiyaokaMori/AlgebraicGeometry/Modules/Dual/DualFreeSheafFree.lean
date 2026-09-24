import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModuleUnit
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.FreeSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesInternalHom
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.FreeModuleStalkBasisSpan
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualSheafOld

/-! # The dual of a free sheaf is free

The dual of a free sheaf of rank `r` is free of rank `r`: `Hom(O_X^r, O_X) ≅ O_X^r`.

Proof route (entirely at the presheaf level, without the monoidal structure or the tensor–Hom
adjunction): `Scheme.Modules.dual M = moduleSheafDual M` is the sheafification of the presheaf
`moduleDualPresheaf M` of compatible families of local functionals; this presheaf is already a sheaf
(`moduleDualPresheaf_isSheaf`), `DualSheaf` packages it directly as `Scheme.Modules.dualSheaf M`, and
`dualSheafIsoOld` (`DualSheafOld`) gives `dualSheaf M ≅ moduleSheafDual M`. So it suffices to prove
`moduleDualPresheaf (O^{(I)}) ≅ O^{(I)}` at the presheaf level: for finite `I` and every open `U`,
  `Γ(O^{(I)}, U) ≃ₗ[Γ(X,U)] Hom_{O_U}(O^{(I)}|_U, O_U)`,  `s ↦ ∑ i, s_i · e_i^∨`,
where `e_i^∨` is the coordinate projection `proj i`. Injectivity and surjectivity both follow from the
expansion of sections in the standard basis (`section_decomp`) and `⟨e_i^∨, e_j⟩ = δ_{ij}`;
compatibility with restriction is the naturality of `proj i`. Finally `PresheafOfModules.isoMk` and
`Scheme.Modules.fullyFaithfulToPresheafOfModules` lift the presheaf isomorphism to `X.Modules`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.DualFreeScratch

open AlgebraicGeometry.Scheme.Modules MiyaokaMori.FreeStalk

variable {X : Scheme.{u}} {I : Type u}

lemma ofUSec_add (U : X.Opens) (a b : Γ(Scheme.Modules.unitModule X, U)) :
    ofUSec U (a + b) = ofUSec U a + ofUSec U b := rfl

lemma ofUSec_smul (U : X.Opens) (r : Γ(X, U)) (a : Γ(Scheme.Modules.unitModule X, U)) :
    ofUSec U (r • a) = r * ofUSec U a := rfl

/-- The `i`-th coordinate. -/
def coord (i : I) {U : X.Opens} (s : Γ(freeM X I, U)) : Γ(X, U) :=
  ofUSec U ((proj X I i).app U s)

lemma coord_add (i : I) {U : X.Opens} (s t : Γ(freeM X I, U)) :
    coord i (s + t) = coord i s + coord i t := by
  simp only [coord, map_add, ofUSec_add]

lemma coord_smul (i : I) {U : X.Opens} (r : Γ(X, U)) (s : Γ(freeM X I, U)) :
    coord i (r • s) = r * coord i s := by
  simp only [coord, Scheme.Modules.Hom.app_smul, ofUSec_smul]

lemma coord_res (i : I) {U V : X.Opens} (h : V ⟶ U) (s : Γ(freeM X I, U)) :
    coord i ((freeM X I).presheaf.map h.op s) = X.presheaf.map h.op (coord i s) :=
  PresheafOfModules.naturality_apply (proj X I i).val h.op s

open Classical in
lemma coord_e (i j : I) (U : X.Opens) : coord i (e I j U) = if j = i then 1 else 0 := by
  have h : (proj X I i).app U ((inc X I j).app U (uSec U 1))
      = ((inc X I j ≫ proj X I i)).app U (uSec U 1) := rfl
  rw [e_eq, coord, h, inc_proj]
  split_ifs <;> rfl

/-- The coordinate as a linear map. -/
def coordLin (i : I) (U : X.Opens) : Γ(freeM X I, U) →ₗ[Γ(X, U)] Γ(X, U) where
  toFun := coord i
  map_add' := coord_add i
  map_smul' r s := coord_smul i r s

/-- The dual basis element `e_i^∨ ∈ Γ((O^{(I)})^∨, U)`. -/
def dualBasisElt (i : I) (U : X.Opens) : LocalDualSections X (freeM X I) U :=
  ⟨fun V => coordLin i V.left, fun _ _ j x => coord_res i j.left x⟩

variable [Fintype I]

/-- The dual section of a section: `s ↦ ⟨-, s⟩ = ∑ i, s_i · e_i^∨`. -/
def ofSecLin (U : X.Opens) :
    Γ(freeM X I, U) →ₗ[Γ(X, U)] LocalDualSections X (freeM X I) U :=
  ∑ i : I, (coordLin i U).smulRight (dualBasisElt i U)

/-- Evaluation on an open, as an additive homomorphism. -/
def evalHom (U : X.Opens) (V : Over U) (x : Γ(freeM X I, V.left)) :
    LocalDualSections X (freeM X I) U →+ Γ(X, V.left) where
  toFun ψ := ψ.1 V x
  map_zero' := rfl
  map_add' _ _ := rfl

lemma ofSecLin_eq (U : X.Opens) (s : Γ(freeM X I, U)) :
    ofSecLin U s = ∑ i : I, coord i s • dualBasisElt i U := by
  simp [ofSecLin, coordLin]

lemma ofSecLin_apply (U : X.Opens) (s : Γ(freeM X I, U)) (V : Over U)
    (x : Γ(freeM X I, V.left)) :
    ((ofSecLin U s).1 V) x = ∑ i : I, X.presheaf.map V.hom.op (coord i s) * coord i x := by
  have h : ((ofSecLin U s).1 V) x = evalHom U V x (ofSecLin U s) := rfl
  rw [h, ofSecLin_eq, map_sum]
  rfl


omit [Fintype I] in
lemma coordLin_apply (i : I) (U : X.Opens) (s : Γ(freeM X I, U)) :
    coordLin i U s = coord i s := rfl

lemma section_decomp' (U : X.Opens) (s : Γ(freeM X I, U)) :
    s = ∑ j : I, coord j s • e I j U :=
  section_decomp I U s

lemma coord_sum_smul_e (U : X.Opens) (a : I → Γ(X, U)) (i : I) :
    coord i (∑ j : I, a j • e I j U) = a i := by
  classical
  have h1 : coord i (∑ j : I, a j • e I j U) = ∑ j : I, a j * coord i (e I j U) := by
    show coordLin i U (∑ j : I, a j • e I j U) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [coordLin_apply, coord_smul]
  rw [h1]
  simp [coord_e]

lemma res_id (U : X.Opens) (r : Γ(X, U)) : X.presheaf.map (𝟙 U).op r = r := by simp

/-- The value of `φ` on the `i`-th basis element over `U`. -/
def topCoeff (U : X.Opens) (φ : LocalDualSections X (freeM X I) U) (i : I) : Γ(X, U) :=
  φ.1 (Over.mk (𝟙 U)) (e I i U)

lemma ofSecLin_at_top (U : X.Opens) (s : Γ(freeM X I, U)) (j : I) :
    topCoeff U (ofSecLin U s) j = coord j s := by
  classical
  show ((ofSecLin U s).1 (Over.mk (𝟙 U))) (e I j U) = coord j s
  rw [ofSecLin_apply]
  simp only [Over.mk_left, Over.mk_hom]
  simp only [res_id]
  rw [Fintype.sum_eq_single j (fun i hi => by rw [coord_e, if_neg (Ne.symm hi), mul_zero])]
  rw [coord_e, if_pos rfl, mul_one]

lemma ofSecLin_injective (U : X.Opens) : Function.Injective (ofSecLin (X := X) (I := I) U) := by
  intro s t hst
  have h : ∀ j : I, coord j s = coord j t := fun j => by
    rw [← ofSecLin_at_top U s j, ← ofSecLin_at_top U t j, hst]
  rw [section_decomp' U s, section_decomp' U t]
  exact Finset.sum_congr rfl fun j _ => by rw [h j]

lemma ofSecLin_surjective (U : X.Opens) : Function.Surjective (ofSecLin (X := X) (I := I) U) := by
  classical
  intro φ
  have hV : ∀ (V : Over U) (i : I),
      X.presheaf.map V.hom.op (topCoeff U φ i) = φ.1 V (e I i V.left) := by
    intro V i
    have hφ := φ.2 V (Over.mk (𝟙 U)) (Over.homMk V.hom (by simp)) (e I i U)
    simp only [Over.homMk_left] at hφ
    have h2 : (freeM X I).presheaf.map V.hom.op (e I i U) = e I i V.left := e_res I i V.hom
    show X.presheaf.map V.hom.op (φ.1 (Over.mk (𝟙 U)) (e I i U)) = φ.1 V (e I i V.left)
    rw [← hφ, h2]
  refine ⟨∑ i : I, topCoeff U φ i • e I i U, ?_⟩
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro x
  have hc : ∀ i : I, coord i (∑ k : I, topCoeff U φ k • e I k U) = topCoeff U φ i :=
    fun i => coord_sum_smul_e U _ i
  have hx : φ.1 V x = ∑ i : I, coord i x * φ.1 V (e I i V.left) := by
    conv_lhs => rw [section_decomp' V.left x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.map_smul, smul_eq_mul]
  rw [ofSecLin_apply, hx]
  exact Finset.sum_congr rfl fun i _ => by rw [hc i, hV V i, mul_comm]

/-- The linear isomorphism on each open. -/
def ofSecEquiv (U : X.Opens) :
    Γ(freeM X I, U) ≃ₗ[Γ(X, U)] LocalDualSections X (freeM X I) U :=
  LinearEquiv.ofBijective (ofSecLin U) ⟨ofSecLin_injective U, ofSecLin_surjective U⟩

lemma ofSecLin_res {U V : X.Opens} (h : V ⟶ U) (s : Γ(freeM X I, U)) :
    ofSecLin V ((freeM X I).presheaf.map h.op s) =
      localDualRestrict (freeM X I) h (ofSecLin U s) := by
  apply Subtype.ext
  funext W
  apply LinearMap.ext
  intro x
  have hL : ((ofSecLin V ((freeM X I).presheaf.map h.op s)).1 W) x
      = ∑ i : I, X.presheaf.map W.hom.op (coord i ((freeM X I).presheaf.map h.op s)) * coord i x :=
    ofSecLin_apply V _ W x
  have hR : ((localDualRestrict (freeM X I) h (ofSecLin U s)).1 W) x
      = ∑ i : I, X.presheaf.map (W.hom ≫ h).op (coord i s) * coord i x :=
    ofSecLin_apply U s ((Over.map h).obj W) x
  rw [hL, hR]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [coord_res, op_comp, X.presheaf.map_comp]
  rfl

lemma ofSecLin_ofSecEquiv_symm (U : X.Opens) (φ : LocalDualSections X (freeM X I) U) :
    ofSecLin U ((ofSecEquiv U).symm φ) = φ := (ofSecEquiv U).apply_symm_apply φ

/-- The isomorphism at the presheaf level. -/
def dualFreePresheafIso :
    AlgebraicGeometry.Scheme.Modules.moduleDualPresheaf (freeM X I) ≅
      (Scheme.Modules.toPresheafOfModules X).obj (freeM X I) :=
  PresheafOfModules.isoMk (fun V => (ofSecEquiv V.unop).symm.toModuleIso) (by
    intro V W j
    ext φ
    apply (ofSecEquiv (unop W)).injective
    show ofSecEquiv (unop W)
          ((ofSecEquiv (unop W)).symm (localDualRestrict (freeM X I) j.unop φ)) =
        ofSecEquiv (unop W)
          ((freeM X I).presheaf.map j.unop.op ((ofSecEquiv (unop V)).symm φ))
    rw [LinearEquiv.apply_symm_apply]
    have h2 : ofSecLin (unop V) ((ofSecEquiv (unop V)).symm φ) = φ :=
      (ofSecEquiv (unop V)).apply_symm_apply φ
    have h1 := ofSecLin_res (X := X) (I := I) j.unop ((ofSecEquiv (unop V)).symm φ)
    rw [h2] at h1
    exact h1.symm)

/-- The isomorphism between the (unsheafified) dual sheaf and the free sheaf. -/
def dualSheafFreeIso : Scheme.Modules.dualSheaf (freeM X I) ≅ freeM X I :=
  (Scheme.Modules.fullyFaithfulToPresheafOfModules (X := X)).preimageIso dualFreePresheafIso

/-- The isomorphism between the sheafified dual and the free sheaf. -/
def moduleSheafDualFreeIso : AlgebraicGeometry.Scheme.Modules.moduleSheafDual (freeM X I) ≅ freeM X I :=
  (Scheme.Modules.dualSheafIsoOld (freeM X I)).symm ≪≫ dualSheafFreeIso

end MiyaokaMori.DualFreeScratch

theorem AlgebraicGeometry.Scheme.Modules.dual_free_iso {X : AlgebraicGeometry.Scheme.{u}} (r : ℕ) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.dual (SheafOfModules.free (R := X.ringCatSheaf) (ULift (Fin r))) ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift (Fin r))) :=
  ⟨MiyaokaMori.DualFreeScratch.moduleSheafDualFreeIso (X := X) (I := ULift.{u} (Fin r))⟩

end
