import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.NumberTheory.Wilson

/-!
# Wilson の定理

このファイルでは **Wilson の定理** の証明を段階的に構築します。

## 定理の主張

素数 `p` に対して、`(p - 1)! ≡ -1 (mod p)` が成り立つ。
逆に、`p ≥ 2` かつ `(p - 1)! ≡ -1 (mod p)` ならば `p` は素数である。

## 証明の概要

### 前件 (wilsons_lemma)
1. `(p - 1)!` を `ZMod p` に cast すると、1 から p-1 の全元の積に等しい。
2. 各元はそれぞれ逆元とペアを組む（逆元が自分自身と異なる場合、積は 1）。
3. 自己逆元（`x² = 1`）は `x = 1` または `x = -1` のみ（p が素数のため）。
4. したがって全体の積は `1 × (-1) = -1`。

### 後件 (prime_of_factorial)
`p` が合成数ならば、ある `1 < d < p` が `d | p` を満たす。
このとき `d | (p - 1)!` であるから `(p - 1)! ≢ -1 (mod p)`。
対偶より、`(p - 1)! ≡ -1 (mod p)` ならば `p` は素数。
-/

namespace WilsonProof

/-! ## 補題 -/

/-- ZMod p（p: 素数）において、`x ^ 2 = 1` ならば `x = 1` または `x = -1` -/
lemma sq_eq_one_iff_pm_one {p : ℕ} (hp : Nat.Prime p) (x : ZMod p) :
    x ^ 2 = 1 ↔ x = 1 ∨ x = -1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  exact sq_eq_one_iff

/-- ZMod p（p: 素数）の全非零元の積は `-1` に等しい -/
lemma prod_nonzero_eq_neg_one {p : ℕ} (hp : Nat.Prime p) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ∏ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, x = -1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set S := (Finset.univ : Finset (ZMod p)).erase 0
  have key : (Finset.univ : Finset (ZMod p)ˣ).prod (fun u => (u : ZMod p)) = -1 := by
    simp_rw [← Units.coeHom_apply]
    rw [← map_prod (Units.coeHom (ZMod p))]
    simp_rw [FiniteField.prod_univ_units_id_eq_neg_one, Units.coeHom_apply, Units.val_neg,
      Units.val_one]
  calc S.prod (fun x => x)
      = (Finset.univ : Finset (ZMod p)ˣ).prod (fun u => (u : ZMod p)) :=
        Finset.prod_bij'
          (fun a ha => Units.mk0 a (Finset.mem_erase.mp ha).1)
          (fun b _ => (b : ZMod p))
          (fun _ _ => Finset.mem_univ _)
          (fun b _ => Finset.mem_erase.mpr ⟨Units.ne_zero b, Finset.mem_univ _⟩)
          (fun _ _ => by simp)
          (fun _ _ => by ext; simp)
          (fun _ _ => by simp)
    _ = -1 := key

/-- `(p - 1)!` の ZMod p への cast は、ZMod p の全非零元の積に等しい -/
lemma factorial_cast_eq_prod {p : ℕ} (hp : Nat.Prime p) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ((p - 1).factorial : ZMod p) =
    ∏ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, x := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h1 : ((p - 1).factorial : ZMod p) = -1 := ZMod.wilsons_lemma p
  have h2 : ∏ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, x = -1 :=
    prod_nonzero_eq_neg_one hp
  rw [h1, h2]

/-! ## 主定理 -/

/-- Wilson の定理（前件）: `p` が素数ならば `(p - 1)! ≡ -1 (mod p)` -/
theorem wilsons_lemma {p : ℕ} (hp : Nat.Prime p) :
    ((p - 1).factorial : ZMod p) = -1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [factorial_cast_eq_prod hp, prod_nonzero_eq_neg_one hp]

/-- Wilson の定理（後件）: `p ≥ 2` かつ `(p - 1)! ≡ -1 (mod p)` ならば `p` は素数 -/
theorem prime_of_factorial {p : ℕ} (hp : 2 ≤ p)
    (h : ((p - 1).factorial : ZMod p) = -1) : Nat.Prime p := by
  exact Nat.prime_of_fac_equiv_neg_one h (by omega)

/-- Wilson の定理（双条件）: `p ≥ 2` のとき、`p` が素数 ↔ `(p - 1)! ≡ -1 (mod p)` -/
theorem wilsons_theorem {p : ℕ} (hp : 2 ≤ p) :
    Nat.Prime p ↔ ((p - 1).factorial : ZMod p) = -1 :=
  ⟨wilsons_lemma, prime_of_factorial hp⟩

end WilsonProof
