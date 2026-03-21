import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Algebra.Module.PID
import Mathlib.Data.ZMod.Basic

/-!
# 有限生成アーベル群の構造定理

このファイルでは **有限生成アーベル群の構造定理** の証明を段階的に構築します。

## 定理の主張

任意の有限生成アーベル群 `G` は次の形に分解される：
  `G ≅ ℤⁿ ⊕ ⨁ᵢ ℤ/(pᵢ^eᵢ)`

ここで `n` は自由部分のランク、`pᵢ` は素数、`eᵢ` は正整数。

## 証明の概要

### 自由部分とねじれ部分の分解
有限生成アーベル群は ℤ-加群とみなせる。ℤ は単項イデアル整域 (PID) であるから、
PID 上の有限生成加群の構造定理を適用すると、自由部分とねじれ部分に分解できる。

### ねじれ部分の素冪巡回群への分解
ねじれ部分は有限アーベル群であり、PID 上のねじれ加群の分解定理により、
素冪位数の巡回群の直和に分解される。

### 有限アーベル群の場合
有限アーベル群では自由部分のランクが 0 となり、
全体が素冪位数の巡回群の直和として表される。
-/

open scoped DirectSum

universe u v

namespace AbelianGroupStructure

/-! ## 基礎補題 -/

/-- ℤ は単項イデアル整域である -/
lemma int_is_pid : IsPrincipalIdealRing ℤ := inferInstance

/-- 有限生成ねじれアーベル群は有限である -/
lemma fg_torsion_is_finite (G : Type u) [AddCommGroup G] [Module ℤ G] [Module.Finite ℤ G]
    (hM : Module.IsTorsion ℤ G) : Finite G :=
  Module.finite_of_fg_torsion G hM

/-! ## ねじれ加群の分解 -/

/-- PID 上の有限生成ねじれ加群は、既約元の冪によるイデアル商の直和に同型である。

ℤ-加群の場合、これは「ねじれアーベル群は素冪位数の巡回群の直和に分解される」ことを意味する。
-/
theorem torsion_module_decomposition (R : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (hM : Module.IsTorsion R M) :
    ∃ (ι : Type u) (_ : Fintype ι) (p : ι → R) (_ : ∀ i, Irreducible (p i)) (e : ι → ℕ),
      Nonempty <| M ≃ₗ[R] ⨁ i : ι, R ⧸ R ∙ p i ^ e i :=
  Module.equiv_directSum_of_isTorsion hM

/-! ## 主定理 -/

/-- PID 上の有限生成加群の構造定理：
自由部分（`Fin n →₀ R`）と、既約元の冪によるイデアル商の直和の積に同型。

これは有限生成アーベル群の構造定理の一般化であり、
`R = ℤ` の場合に「`G ≅ ℤⁿ ⊕ ⨁ᵢ ℤ/(pᵢ^eᵢ)`」を与える。
-/
theorem structure_theorem_pid (R : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ∃ (n : ℕ) (ι : Type u) (_ : Fintype ι) (p : ι → R) (_ : ∀ i, Irreducible (p i)) (e : ι → ℕ),
      Nonempty <| M ≃ₗ[R] (Fin n →₀ R) × ⨁ i : ι, R ⧸ R ∙ p i ^ e i :=
  Module.equiv_free_prod_directSum R M

/-- 有限生成アーベル群の構造定理：
任意の有限生成アーベル群 `G` は、自由アーベル群 `ℤⁿ` と
素冪位数の巡回群 `ℤ/(pᵢ^eᵢ)` の直和の積に同型である。
-/
theorem structure_theorem_fg_abelian (G : Type u) [AddCommGroup G] [AddGroup.FG G] :
    ∃ (n : ℕ) (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime (p i)) (e : ι → ℕ),
      Nonempty <| G ≃+ (Fin n →₀ ℤ) × ⨁ i : ι, ZMod (p i ^ e i) :=
  AddCommGroup.equiv_free_prod_directSum_zmod G

/-- 有限アーベル群の構造定理：
任意の有限アーベル群 `G` は、素冪位数の巡回群 `ℤ/(pᵢ^eᵢ)` の直和に同型である。
（自由部分のランクは 0。）
-/
theorem structure_theorem_finite_abelian (G : Type u) [AddCommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime (p i)) (e : ι → ℕ),
      Nonempty <| G ≃+ ⨁ i : ι, ZMod (p i ^ e i) :=
  AddCommGroup.equiv_directSum_zmod_of_finite G

/-- 有限アーベル群の構造定理（自然数版）：
任意の有限アーベル群 `G` は、位数が 2 以上の巡回群 `ℤ/(nᵢ)` の直和に同型である。
-/
theorem structure_theorem_finite_abelian' (G : Type*) [AddCommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
      (∀ i, 1 < n i) ∧ Nonempty (G ≃+ ⨁ i, ZMod (n i)) :=
  AddCommGroup.equiv_directSum_zmod_of_finite' G

end AbelianGroupStructure
