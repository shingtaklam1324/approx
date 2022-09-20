import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormCast

/-!
# Dyadic rationals

In this file, we define dyadic rationals
-/

structure Dyadic where
  mantissa : Int
  exponent : Int
  coprime : (mantissa = 0 ∧ exponent = 0) ∨ mantissa.natAbs.coprime 2
  deriving DecidableEq

instance : Inhabited Dyadic := ⟨⟨1, 0, Or.inr (by rfl)⟩⟩

lemma Dyadic.eq_iff (d₁ d₂ : Dyadic) : 
  d₁ = d₂ ↔ d₁.mantissa = d₂.mantissa ∧ d₁.exponent = d₂.exponent :=
⟨λ h => ⟨h ▸ rfl, h ▸ rfl⟩, λ ⟨h₁, h₂⟩ => by
  cases d₁
  cases d₂
  simp at * -- non-terminal simp
  apply And.intro
  · exact h₁
  · exact h₂⟩

instance : ToString Dyadic where
  toString a := s!"{a.mantissa} * 2^{a.exponent}"

-- instance : Repr Dyadic where
--   reprPrec a _ := s!"⟨{a.mantissa}, {a.exponent}⟩"

section Rat

def Rat.pow (a : Rat) : Nat → Rat
  | 0 => 1
  | n+1 => a.pow n * a

instance : Pow Rat Nat := ⟨Rat.pow⟩

instance : Pow Rat Int where
  pow a | Int.ofNat n => a ^ n 
        | Int.negSucc n => (1 / a) ^ (n + 1)

def Dyadic.toRat (d : Dyadic) : Rat :=
  d.mantissa * (2 : Rat) ^ d.exponent
  
end Rat

private lemma Nat.two_dvd_or_coprime_two (n : ℕ) : 2 ∣ n ∨ n.coprime 2 :=
  let m := gcd 2 n
  have hmpos : 0 < m := gcd_pos_of_pos_left _ <| by decide
  have hm2 : m ≤ 2 := gcd_le_left _ <| by decide
  have hm : m = gcd 2 n := rfl
  match m with
  | 0 => absurd hmpos <| not_lt.2 <| le_refl _
  | 1 => Or.inr <| coprime_comm.1 hm.symm
  | 2 => Or.inl <| hm.symm ▸ gcd_dvd_right 2 n
  | (k + 3) => 
    have : 3 ≤ k + 3 := le_add_left _ _
    have : 3 ≤ 2 := le_trans this hm2
    False.elim <| by norm_num at this; exact this

def Dyadic.mk' (m e : Int) : Dyadic :=
  if hm : m = 0 then
    ⟨0, 0, by decide⟩
  else if hm2 : 2 ∣ m then
    have : m.natAbs / (2 : Int).natAbs < m.natAbs := 
      Nat.div_lt_self (Int.natAbs_pos.2 hm) (by decide)
    Dyadic.mk' (m / 2) (e + 1)
  else
    ⟨m, e, Or.inr <| Nat.two_dvd_or_coprime_two m.natAbs |>.resolve_left <| by
      rw [←Int.dvd_natAbs, show (2 : Int) = (2 : Nat) by norm_num] at hm2
      intro ⟨x, hx⟩
      rw [hx] at hm2
      exact hm2 ⟨x, by norm_cast⟩
    ⟩
  termination_by _ => m.natAbs

def Dyadic.add (d₁ d₂ : Dyadic) : Dyadic := 
  Dyadic.mk'
    (d₁.mantissa * 2 ^ (d₁.exponent - d₂.exponent).toNat + 
      d₂.mantissa * 2 ^ (d₂.exponent - d₁.exponent).toNat)
    (min d₁.exponent d₂.exponent)

instance : Add Dyadic := ⟨Dyadic.add⟩

private lemma Dyadic.add_eq (d₁ d₂ : Dyadic) : 
  d₁ + d₂ = Dyadic.mk' 
    (d₁.mantissa * 2 ^ (d₁.exponent - d₂.exponent).toNat + 
      d₂.mantissa * 2 ^ (d₂.exponent - d₁.exponent).toNat)
    (min d₁.exponent d₂.exponent) := rfl

def Dyadic.mul (d₁ d₂ : Dyadic) : Dyadic :=
  Dyadic.mk' (d₁.mantissa * d₂.mantissa) (d₁.exponent + d₂.exponent)

instance : Mul Dyadic := ⟨Dyadic.mul⟩

private lemma Dyadic.mul_eq (d₁ d₂ : Dyadic) : 
  d₁ * d₂ = Dyadic.mk' (d₁.mantissa * d₂.mantissa) (d₁.exponent + d₂.exponent) 
:= rfl


def Dyadic.neg (d : Dyadic) : Dyadic where
  mantissa := -d.mantissa
  exponent := d.exponent
  coprime := d.coprime.elim (λ ⟨h₁, h₂⟩ => Or.inl ⟨by simp [h₁], h₂⟩)
    (λ h => Or.inr <| by rwa [Int.natAbs_neg])

instance : Neg Dyadic := ⟨Dyadic.neg⟩

instance : Zero Dyadic := ⟨⟨0, 0, Or.inl <| by decide⟩⟩

instance : One Dyadic := ⟨⟨1, 0, Or.inr <| by rfl⟩⟩

instance : OfNat Dyadic n := ⟨Dyadic.mk' n 0⟩

def Dyadic.div₂ (d : Dyadic) (n : Nat) : Dyadic :=
  Dyadic.mk' d.mantissa (d.exponent - n)

#eval (3 : Dyadic).div₂ 4 + (4 : Dyadic)

example : (3 : Dyadic).div₂ 4 + (4 : Dyadic) = (67 : Dyadic).div₂ 4 := by rfl

def Dyadic.lt (d₁ d₂ : Dyadic) : Prop :=
  (d₁.mantissa * 2 ^ (d₁.exponent - d₂.exponent).natAbs) <
  (d₂.mantissa * 2 ^ (d₂.exponent - d₁.exponent).natAbs)

instance : LT Dyadic := ⟨Dyadic.lt⟩

def Dyadic.le (d₁ d₂ : Dyadic) : Prop :=
  (d₁.mantissa * 2 ^ (d₁.exponent - d₂.exponent).natAbs) ≤
  (d₂.mantissa * 2 ^ (d₂.exponent - d₁.exponent).natAbs)

instance : LE Dyadic := ⟨Dyadic.le⟩

namespace Dyadic

@[simp]
lemma mantissa_zero : (0 : Dyadic).mantissa = 0 := rfl

lemma eq_zero_iff_mantissa_eq_zero (d : Dyadic) :
  d = 0 ↔ d.mantissa = 0 := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    rw [d.eq_iff]
    constructor
    · rw [h]
      rfl
    · cases d.coprime with
      | inl h₁ => 
        rw [h₁.2]
        rfl
      | inr h₁ => 
        rw [h, Nat.coprime_iff_gcd_eq_one, Int.natAbs_zero, 
          Nat.gcd_zero_left] at h₁
        norm_num at h₁
        exact h₁.elim

lemma zero_mul (d : Dyadic) : 0 * d = 0 := by
  rw [Dyadic.mul_eq, mantissa_zero, Int.zero_mul]
  rfl

lemma mul_zero (d : Dyadic) : d * 0 = 0 := by
  rw [Dyadic.mul_eq, mantissa_zero, Int.mul_zero]
  rfl

lemma mul_comm (d₁ d₂ : Dyadic) : d₁ * d₂ = d₂ * d₁ := by
  rw [Dyadic.mul_eq, Dyadic.mul_eq, Int.mul_comm, Int.add_comm]

end Dyadic

-- instance : CommRing ℤ where
--   zero_mul := Int.zero_mul
--   mul_zero := Int.mul_zero
--   mul_comm := Int.mul_comm
--   left_distrib := Int.mul_add
--   right_distrib := Int.add_mul
--   mul_one := Int.mul_one
--   one_mul := Int.one_mul
--   npow (n x) := x ^ n
--   npow_zero' n := rfl
--   npow_succ' n x := by rw [Int.mul_comm]; rfl
--   mul_assoc := Int.mul_assoc
--   add_comm := Int.add_comm
--   add_assoc := Int.add_assoc
--   add_zero := Int.add_zero
--   zero_add := Int.zero_add
--   add_left_neg := Int.add_left_neg
--   nsmul := (·*·)
--   nsmul_zero' := Int.zero_mul
--   nsmul_succ' n x := by
--     show ofNat (Nat.succ n) * x = x + ofNat n * x
--     rw [Int.ofNat_succ, Int.add_mul, Int.add_comm, Int.one_mul]
--   sub_eq_add_neg a b := Int.sub_eq_add_neg
--   gsmul := HMul.hMul
--   gsmul_zero' := Int.zero_mul
--   gsmul_succ' n x := by rw [Int.ofNat_succ, Int.add_mul, Int.add_comm, Int.one_mul]
--   gsmul_neg' n x := by
--     cases x with
--     | ofNat m =>
--       rw [Int.negSucc_ofNat_ofNat, Int.ofNat_mul_ofNat]
--       exact rfl
--     | negSucc m =>
--       rw [Int.mul_negSucc_ofNat_negSucc_ofNat, Int.ofNat_mul_negSucc_ofNat]
--       exact rfl
--   natCast := (·)
--   natCast_zero := rfl
--   natCast_succ _ := rfl
--   intCast := (·)
--   intCast_ofNat _ := rfl
--   intCast_negSucc _ := rfl
