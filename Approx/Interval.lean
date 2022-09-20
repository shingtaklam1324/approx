import Approx.Dyadic

structure Interval where
  lb : Dyadic
  ub : Dyadic
  lb_le_ub : lb ≤ ub
  deriving DecidableEq

instance : Membership Dyadic Interval where
  mem x i := i.lb ≤ x ∧ x ≤ i.ub

def Interval.add (i₁ i₂ : Interval) : Interval where
  lb := i₁.lb + i₂.lb
  ub := i₁.ub + i₂.ub
  lb_le_ub := sorry

instance : Add Interval where
  add := Interval.add

def Interval.mul (i₁ i₂ : Interval) : Interval where
  lb := min (min (i₁.lb * i₂.lb) (i₁.lb * i₂.ub)) (min (i₁.ub * i₂.lb) (i₁.ub * i₂.ub))
  ub := max (max (i₁.lb * i₂.lb) (i₁.lb * i₂.ub)) (max (i₁.ub * i₂.lb) (i₁.ub * i₂.ub))
  lb_le_ub := sorry

instance : Mul Interval where
  mul := Interval.mul

def Interval.sub (i₁ i₂ : Interval) : Interval where
  lb := i₁.lb - i₂.ub
  ub := i₁.ub - i₂.lb
  lb_le_ub := sorry

instance : Sub Interval where
  sub := Interval.sub

def length (i : Interval) : Dyadic := i.ub - i.lb

/-
Correctness of the interval operations
-/

namespace Interval

lemma mem_add {i₁ i₂ : Interval} {a₁ a₂ : Dyadic} (h₁ : a₁ ∈ i₁) (h₂ : a₂ ∈ i₂) : 
a₁ + a₂ ∈ i₁ + i₂ := sorry

lemma mem_mul {i₁ i₂ : Interval} {a₁ a₂ : Dyadic} (h₁ : a₁ ∈ i₁) (h₂ : a₂ ∈ i₂) :
a₁ * a₂ ∈ i₁ * i₂ := sorry

end Interval
