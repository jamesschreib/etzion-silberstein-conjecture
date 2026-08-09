import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic

/-!
# A counterexample to universal attainment of the Etzion--Silberstein bound

This file formalizes the Ferrers diagram `(3, 3, 5, 5, 5)` at minimum
rank distance five over `F_169`.  It verifies the numerical bound, constructs
a two-dimensional code from multiplication in a degree-five extension, and
reduces the upper bound to the named geometric input
`quinticObstruction_external`.
-/

set_option autoImplicit false

open Finset BigOperators Module

namespace EtzionSilbersteinCounterexample

abbrev Row := Fin 5
abbrev Column := Fin 5

/-- The column heights of the counterexample Ferrers diagram. -/
def columnHeight : Column → ℕ := ![3, 3, 5, 5, 5]

/-- A matrix is supported on the Ferrers diagram when entries below each
column's prescribed height vanish.  Rows and columns are numbered from zero. -/
def IsSupported {F : Type*} [Zero F] (A : Matrix Row Column F) : Prop :=
  ∀ i j, columnHeight j ≤ i.1 → A i j = 0

/-- The `j`-th quantity in the Etzion--Silberstein bound for distance five. -/
def boundTerm (j : Fin 5) : ℕ :=
  ∑ i : Fin 5,
    if i.1 < 5 - j.1 then columnHeight i - (4 - j.1) else 0

/-- The Etzion--Silberstein bound, minimized over the five deletion choices. -/
def etzionSilbersteinBound : ℕ :=
  (Finset.univ.image boundTerm).min' (by simp)

/-- The five bound terms are `3, 4, 5, 4, 3`. -/
theorem boundTerm_values : List.ofFn boundTerm = [3, 4, 5, 4, 3] := by
  native_decide

/-- The numerical Etzion--Silberstein bound for the diagram is three. -/
theorem etzionSilbersteinBound_eq_three : etzionSilbersteinBound = 3 := by
  native_decide

section Codes

variable {F : Type*} [Field F]

abbrev SquareMatrix (F : Type*) [Field F] := Matrix Row Column F

/-- A linear Ferrers-diagram rank-metric code of minimum rank distance five.
For a `5 × 5` matrix, nonzero determinant is equivalent to rank five. -/
def IsRankFiveCode (C : Submodule F (SquareMatrix F)) : Prop :=
  (∀ A ∈ C, IsSupported A) ∧
    ∀ A ∈ C, A ≠ 0 → Matrix.det A ≠ 0

/-- `k` is the optimal dimension when it is attained and bounds every code. -/
def IsOptimalDimension (k : ℕ) : Prop :=
  (∃ C : Submodule F (SquareMatrix F),
      IsRankFiveCode C ∧ Module.finrank F C = k) ∧
    ∀ C : Submodule F (SquareMatrix F),
      IsRankFiveCode C → Module.finrank F C ≤ k

/-- Attainment of the Etzion--Silberstein bound for the fixed diagram and
distance. -/
def AttainsEtzionSilbersteinBound : Prop :=
  ∃ C : Submodule F (SquareMatrix F),
    IsRankFiveCode C ∧
      Module.finrank F C = etzionSilbersteinBound

end Codes

/-! ## The field and the two-dimensional construction -/

/-- A canonical model of the field with `13² = 169` elements. -/
instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

abbrev F169 := GaloisField 13 2

noncomputable instance : Fintype F169 := Fintype.ofFinite F169

theorem card_F169 : Fintype.card F169 = 169 := by
  rw [Fintype.card_eq_nat_card]
  simpa [F169] using GaloisField.card 13 2 (by norm_num : (2 : ℕ) ≠ 0)

namespace Construction

/-- A degree-five extension of `F_169`. -/
abbrev E := FiniteField.Extension F169 13 5

/-- A power basis `1, α, ..., α⁴` for the degree-five extension. -/
noncomputable def powerBasis : PowerBasis F169 E :=
  Field.powerBasisOfFiniteOfSeparable F169 E

theorem powerBasis_dim : powerBasis.dim = 5 := by
  rw [← powerBasis.finrank, FiniteField.finrank_extension F169 13 5]

/-- The power basis reindexed by the literal type `Fin 5`. -/
noncomputable def basis : Basis (Fin 5) F169 E :=
  powerBasis.basis.reindex (finCongr powerBasis_dim)

theorem basis_apply (i : Fin 5) : basis i = powerBasis.gen ^ (i : ℕ) := by
  simp [basis, PowerBasis.coe_basis]

theorem basis_zero : basis 0 = 1 := by
  rw [basis_apply]
  simp

theorem basis_one : basis 1 = powerBasis.gen := by
  rw [basis_apply]
  simp

theorem basis_two : basis 2 = powerBasis.gen ^ 2 := by
  rw [basis_apply]
  change powerBasis.gen ^ (2 : ℕ) = powerBasis.gen ^ (2 : ℕ)
  rfl

/-- The two-dimensional coefficient space `a + bα`, expressed using the first
two power-basis vectors. -/
noncomputable def coefficientMap : F169 × F169 →ₗ[F169] E :=
  LinearMap.coprod
    ((LinearMap.id : F169 →ₗ[F169] F169).smulRight (basis 0))
    ((LinearMap.id : F169 →ₗ[F169] F169).smulRight (basis 1))

theorem coefficientMap_apply (x : F169 × F169) :
    coefficientMap x = x.1 • basis 0 + x.2 • basis 1 :=
  rfl

theorem coefficientMap_coord_zero (x : F169 × F169) :
    basis.repr (coefficientMap x) 0 = x.1 := by
  rw [coefficientMap_apply, map_add, map_smul, map_smul,
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Basis.repr_self_apply, Basis.repr_self_apply]
  norm_num

theorem coefficientMap_coord_one (x : F169 × F169) :
    basis.repr (coefficientMap x) 1 = x.2 := by
  rw [coefficientMap_apply, map_add, map_smul, map_smul,
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Basis.repr_self_apply, Basis.repr_self_apply]
  norm_num

theorem coefficientMap_injective : Function.Injective coefficientMap := by
  intro x y hxy
  apply Prod.ext
  · have h := congr_arg (fun z : E => basis.repr z 0) hxy
    simpa only [coefficientMap_coord_zero] using h
  · have h := congr_arg (fun z : E => basis.repr z 1) hxy
    simpa only [coefficientMap_coord_one] using h

/-- The left-regular representation of `a + bα` in the power basis. -/
noncomputable def constructionMap :
    F169 × F169 →ₗ[F169] SquareMatrix F169 :=
  (Algebra.leftMulMatrix basis).toLinearMap.comp coefficientMap

theorem constructionMap_apply (x : F169 × F169) :
    constructionMap x = Algebra.leftMulMatrix basis (coefficientMap x) :=
  rfl

theorem constructionMap_injective : Function.Injective constructionMap :=
  (Algebra.leftMulMatrix_injective basis).comp coefficientMap_injective

/-- The promised two-dimensional multiplication code. -/
noncomputable def code : Submodule F169 (SquareMatrix F169) :=
  LinearMap.range constructionMap

theorem code_finrank : Module.finrank F169 code = 2 := by
  let e : (F169 × F169) ≃ₗ[F169] code :=
    LinearEquiv.ofInjective constructionMap constructionMap_injective
  calc
    Module.finrank F169 code = Module.finrank F169 (F169 × F169) := e.finrank_eq.symm
    _ = 2 := by simp [Module.finrank_prod]

theorem leftMulMatrix_det_ne_zero {x : E} (hx : x ≠ 0) :
    Matrix.det (Algebra.leftMulMatrix basis x) ≠ 0 := by
  rw [← Algebra.norm_eq_matrix_det basis]
  exact Algebra.norm_ne_zero_iff_of_basis basis |>.2 hx

theorem coefficientMap_mul_basis_zero (x : F169 × F169) :
    coefficientMap x * basis 0 =
      x.1 • basis 0 + x.2 • basis 1 := by
  rw [coefficientMap_apply, basis_zero, mul_one]

theorem coefficientMap_mul_basis_one (x : F169 × F169) :
    coefficientMap x * basis 1 =
      x.1 • basis 1 + x.2 • basis 2 := by
  rw [coefficientMap_apply, add_mul]
  rw [smul_mul_assoc, smul_mul_assoc, basis_zero, one_mul,
    basis_one, basis_two, pow_two]

theorem repr_two_basis_eq_zero (a b : F169) (r s i : Fin 5)
    (hri : r ≠ i) (hsi : s ≠ i) :
    basis.repr (a • basis r + b • basis s) i = 0 := by
  rw [map_add, map_smul, map_smul,
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Basis.repr_self_apply, Basis.repr_self_apply, if_neg hri, if_neg hsi]
  simp

theorem code_supported : ∀ A ∈ code, IsSupported A := by
  rintro A ⟨x, rfl⟩ i j hij
  rw [constructionMap_apply, Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases j
  · change basis.repr (coefficientMap x * basis 0) i = 0
    rw [coefficientMap_mul_basis_zero]
    apply repr_two_basis_eq_zero
    · intro h
      subst i
      norm_num [columnHeight] at hij
    · intro h
      subst i
      norm_num [columnHeight] at hij
  · change basis.repr (coefficientMap x * basis 1) i = 0
    rw [coefficientMap_mul_basis_one]
    apply repr_two_basis_eq_zero
    · intro h
      subst i
      norm_num [columnHeight] at hij
    · intro h
      subst i
      norm_num [columnHeight] at hij
  · norm_num [columnHeight] at hij
    exact (Nat.not_le_of_lt i.isLt hij).elim
  · norm_num [columnHeight] at hij
    exact (Nat.not_le_of_lt i.isLt hij).elim
  · norm_num [columnHeight] at hij
    exact (Nat.not_le_of_lt i.isLt hij).elim

theorem code_full_rank :
    ∀ A ∈ code, A ≠ 0 → Matrix.det A ≠ 0 := by
  rintro A ⟨x, rfl⟩ hA
  apply leftMulMatrix_det_ne_zero
  intro hx
  apply hA
  rw [constructionMap_apply, hx, map_zero]

/-- The degree-five extension construction supplies a two-dimensional code. -/
theorem twoDimensionalCode : IsRankFiveCode code :=
  ⟨code_supported, code_full_rank⟩

end Construction

/-! ## The geometric upper bound -/

/-- The upper-bound statement proved in `proof.pdf`: no supported
three-dimensional space can consist entirely of invertible nonzero matrices. -/
def QuinticObstruction : Prop :=
  ∀ C : Submodule F169 (SquareMatrix F169),
    IsRankFiveCode C → Module.finrank F169 C ≤ 2

/-- The determinant-quintic/Hasse--Weil argument in `proof.pdf`, isolated as the
single external mathematical input of this lightweight formalization. -/
axiom quinticObstruction_external : QuinticObstruction

/-- The optimum code dimension for the counterexample is exactly two. -/
theorem optimalDimension_F169 : IsOptimalDimension (F := F169) 2 :=
  ⟨⟨Construction.code, Construction.twoDimensionalCode,
      Construction.code_finrank⟩,
    quinticObstruction_external⟩

/-- The Etzion--Silberstein bound is not attained for this field and diagram. -/
theorem counterexample_to_universal_attainment :
    ¬ AttainsEtzionSilbersteinBound (F := F169) := by
  rintro ⟨C, hC, hdim⟩
  have hupper := quinticObstruction_external C hC
  rw [etzionSilbersteinBound_eq_three] at hdim
  omega

/-- A compact statement of the strict gap `κ = 2 < 3 = ν_min`. -/
theorem counterexample_summary :
    IsOptimalDimension (F := F169) 2 ∧
      etzionSilbersteinBound = 3 ∧
      (2 : ℕ) < etzionSilbersteinBound := by
  exact ⟨optimalDimension_F169, etzionSilbersteinBound_eq_three, by
    rw [etzionSilbersteinBound_eq_three]
    norm_num⟩

end EtzionSilbersteinCounterexample
