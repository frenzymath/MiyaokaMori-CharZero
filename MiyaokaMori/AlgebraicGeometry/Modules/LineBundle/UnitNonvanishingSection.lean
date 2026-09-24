import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus

/-! # The unit section of the structure sheaf is nowhere vanishing

Statement: the germ of the global section `1` of the structure sheaf `O_X` (`SheafOfModules.unit X.ringCatSheaf`)
is nonzero at every point; and at a point with `𝔪_x = ⊥` (i.e. `O_{X,x}` a field, e.g. the generic point of an
integral scheme), a section of a line bundle has nonzero germ iff the point lies in its nonvanishing locus.
Together: the generic point `ξ` of an integral scheme lies in `(O_X).nonvanishingLocus 1`.

Proof:
1. `Γ(O_X, U)` and `Γ(X, U)` coincide verbatim (the underlying presheaf of `SheafOfModules.unit` is the
   structure sheaf through `forget₂`), and the restriction maps are those of the ring, so they send `1` to `1`.
2. If `germ_⊤ 1 = 0 = germ_⊤ 0`, then `TopCat.Presheaf.germ_eq` (stalks of `Ab`-valued presheaves are
   filtered colimits) gives an open neighbourhood `W` of `x` on which `1|_W = 0|_W`, i.e. `1 = 0` in
   `Γ(X, W)`; but `x ∈ W` so `W` is nonempty and `AlgebraicGeometry.Scheme.component_nontrivial` gives
   `Nontrivial Γ(X, W)`, a contradiction.
3. If `𝔪_x = ⊥` then `𝔪_x • ⊤ = ⊥` (`Submodule.bot_smul`), so `germ ∉ 𝔪_x • ⊤ ↔ germ ≠ 0`, and the
   description of the nonvanishing locus concludes.
4. At the generic point `ξ` of an integral scheme `X`, `O_{X,ξ} = X.functionField` is a field (the `Field`
   instance of `Scheme.functionField`), so `𝔪_ξ = ⊥` (`IsLocalRing.maximalIdeal_eq_bot`).

Reference: the definition of `X_s` in Stacks 01CY and the maximal ideal of a local ring.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- For the structure sheaf viewed as a module, the germ of the global section `1` at any point is nonzero. -/
theorem AlgebraicGeometry.Scheme.Modules.germ_unit_one_ne_zero
    (X : AlgebraicGeometry.Scheme.{u}) (x : X) :
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.germ ⊤ x trivial
      (1 : Γ(X, ⊤)) ≠ 0 := by
  intro h
  set F := (show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf with hF
  have h0 : F.germ ⊤ x trivial (1 : Γ(X, ⊤)) = F.germ ⊤ x trivial (0 : Γ(X, ⊤)) := by
    rw [h]; exact (map_zero _).symm
  obtain ⟨W, hxW, iU, iV, hW⟩ :=
    TopCat.Presheaf.germ_eq F (U := ⊤) (V := ⊤) x trivial trivial _ _ h0
  -- the restriction maps of `F` are those of the structure sheaf (verbatim), sending 1 to 1 and 0 to 0
  have key : ((X.presheaf.map iU.op).hom (1 : Γ(X, ⊤)) : Γ(X, W)) =
      ((X.presheaf.map iV.op).hom (0 : Γ(X, ⊤)) : Γ(X, W)) := hW
  rw [map_one, map_zero] at key
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  exact one_ne_zero key

/-- When `𝔪_x = ⊥`, a nonzero germ means membership in the nonvanishing locus. -/
theorem AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_of_maximalIdeal_eq_bot
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤)) (x : X)
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk x) = ⊥)
    (hs : L.presheaf.germ ⊤ x trivial s ≠ 0) :
    x ∈ L.nonvanishingLocus s := by
  rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus, hm, Submodule.bot_smul]
  intro hmem
  exact hs ((Submodule.mem_bot _).mp hmem)

/-- At the generic point of an integral scheme the local ring is the function field, whose maximal ideal is zero. -/
theorem AlgebraicGeometry.maximalIdeal_stalk_genericPoint_eq_bot
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] :
    IsLocalRing.maximalIdeal (X.presheaf.stalk (genericPoint X)) = ⊥ :=
  IsLocalRing.maximalIdeal_eq_bot (R := X.functionField)

/-- On an integral scheme the global section `1` of the structure sheaf is nonzero at the generic point, i.e.
the generic point lies in its nonvanishing locus. -/
theorem AlgebraicGeometry.Scheme.Modules.genericPoint_mem_nonvanishingLocus_unit_one
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    [(show X.Modules from SheafOfModules.unit X.ringCatSheaf).IsLineBundle] :
    genericPoint X ∈
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf).nonvanishingLocus (1 : Γ(X, ⊤)) :=
  AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_of_maximalIdeal_eq_bot _ _ _
    (AlgebraicGeometry.maximalIdeal_stalk_genericPoint_eq_bot X)
    (AlgebraicGeometry.Scheme.Modules.germ_unit_one_ne_zero X (genericPoint X))

end
