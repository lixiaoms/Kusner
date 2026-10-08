import Kusner5.Basic

/-!
The explicit ten-point lower witness for the ORIGINAL five-coordinate Manhattan
distance. This lemma alone is not the original eleven-point exclusion.
-/
namespace Kusner5

noncomputable section

def tenPoint (i : Fin 10) : Point 5 := fun k =>
  if i.val < 5 then
    if k.val = i.val then (1 / 2 : ℝ) else 0
  else
    if k.val = i.val - 5 then (-1 / 2 : ℝ) else 0

set_option maxHeartbeats 1000000 in
theorem tenPoint_unit_equilateral : UnitEquilateral tenPoint := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    norm_num [tenPoint, l1dist, Fin.sum_univ_succ] at *

theorem tenPoint_injective : Function.Injective tenPoint :=
  unitEquilateral_injective tenPoint_unit_equilateral

end
end Kusner5

