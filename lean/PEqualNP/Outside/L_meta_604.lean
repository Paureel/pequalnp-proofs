import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Elim
import PEqualNP.MetaComplexity.Helpers.ReadersExport

namespace PEqualNP.Outside.L_meta_604

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers

private def xorGates (flip : Bool) (width i j : ℕ) : List Gate :=
  if flip then
    [⟨.or, [i, j]⟩, ⟨.and, [i, j]⟩, ⟨.not, [width]⟩,
      ⟨.or, [width + 1, width + 2]⟩]
  else
    [⟨.or, [i, j]⟩, ⟨.and, [i, j]⟩, ⟨.not, [width + 1]⟩,
      ⟨.and, [width, width + 2]⟩]

private theorem xorGates_eval (flip : Bool) (w : List Bool) (i j : ℕ)
    (hi : i < w.length) (hj : j < w.length) :
    (wiresFrom (xorGates flip w.length i j) w).getD (w.length + 3) false =
      xor (w.getD i false) (xor flip (w.getD j false)) := by
  have hprefix (tail : List Bool) (k : ℕ) (hk : k < w.length) :
      (w ++ tail)[k]?.getD false = w[k]?.getD false := by
    rw [List.getElem?_append_left hk]
  cases flip <;> simp [xorGates, wiresFrom, GateOp.eval, hprefix _ _ hi, hprefix _ _ hj] <;>
    cases w[i]?.getD false <;> cases w[j]?.getD false <;> rfl

private theorem appendXor (n s : ℕ) (g : (Fin n → Bool) → Bool) (flip : Bool)
    (hne : ∃ y y', g y ≠ g y') (hc : HasCircuitSize n g s) :
    HasCircuitSize (n + 1)
      (fun x => xor (x (Fin.last n)) (xor flip (g (fun i : Fin n => x i.castSucc)))) (s + 4) := by
  have lifted : HasCircuitSize (n + 1) (fun x => g (fun i : Fin n => x i.castSucc)) s :=
    PermInputs.relabel_size Fin.castSucc g s hc
  obtain ⟨C, hOk, hsz, heval⟩ := lifted
  let width := n + 1 + C.gates.length
  have width_eq (x : Fin (n + 1) → Bool) : (wiresFrom C.gates (List.ofFn x)).length = width := by
    simp [width, length_wiresFrom]
  have ho : C.output < width := by
    by_contra hn
    have hz (y : Fin n → Bool) : g y = false := by
      have he := heval (Fin.snoc y false)
      rw [Circuit.eval, wires_eq, List.getD_eq_default _ _ (by rw [width_eq]; omega)] at he
      simpa using he.symm
    obtain ⟨y, y', hyy'⟩ := hne
    exact hyy' ((hz y).trans (hz y').symm)
  refine ⟨⟨C.gates ++ xorGates flip width n C.output, width + 3⟩, ?_, ?_, ?_⟩
  · intro gate hgate
    rcases List.mem_append.1 hgate with h | h
    · exact hOk gate h
    · cases flip <;> simp only [xorGates, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false] at h <;>
        rcases h with rfl | rfl | rfl | rfl <;> simp
  · have hlen : C.gates.length ≤ s := hsz
    cases flip <;> simp [Circuit.size, xorGates] <;> omega
  · intro x
    let w := wiresFrom C.gates (List.ofFn x)
    have hw : w.length = width := width_eq x
    have hi : n < w.length := by rw [hw]; dsimp [width]; omega
    have hj : C.output < w.length := by rwa [hw]
    have hfresh : w.getD n false = x (Fin.last n) := by
      change (wiresFrom C.gates (List.ofFn x)).getD n false = _
      rw [getD_wiresFrom _ _ _ (by simp)]
      simp
    have hbase : w.getD C.output false = g (fun i : Fin n => x i.castSucc) := heval x
    change (wiresFrom (C.gates ++ xorGates flip width n C.output) (List.ofFn x)).getD
      (width + 3) false = _
    rw [wiresFrom_append]
    change (wiresFrom (xorGates flip width n C.output) w).getD (width + 3) false = _
    rw [← hw, xorGates_eval flip w n C.output hi hj, hfresh, hbase]

private theorem upperBound (n s : ℕ) (g : (Fin n → Bool) → Bool)
    (hne : ∃ y y', g y ≠ g y')
    (hc : HasCircuitSize n g s ∨ HasCircuitSize n (fun y => !(g y)) s) :
    HasCircuitSize (n + 1) (fun x => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4) := by
  rcases hc with h | h
  · simpa using appendXor n s g false hne h
  · have hne' : ∃ y y', !(g y) ≠ !(g y') := by
      obtain ⟨y, y', hy⟩ := hne
      exact ⟨y, y', by simpa using hy⟩
    simpa using appendXor n s (fun y => !(g y)) true hne' h

private theorem lowerBoundTwo (n s : ℕ) (g : (Fin n → Bool) → Bool)
    (hne : ∃ y y', g y ≠ g y')
    (hc : HasCircuitSize (n + 1) (fun x => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 2)) :
    HasCircuitSize n g s ∨ HasCircuitSize n (fun y => !(g y)) s := by
  let f := fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))
  have hlast (x : Fin (n + 1) → Bool) (b : Bool) :
      f (Function.update x (Fin.last n) b) = xor b (g (fun i : Fin n => x i.castSucc)) := by
    have rest : (fun i : Fin n => Function.update x (Fin.last n) b i.castSucc) =
        (fun i : Fin n => x i.castSucc) := by
      funext i
      rw [Function.update_of_ne]
      intro he
      have hn := congrArg Fin.val he
      have hi := i.isLt
      simp at hn
      omega
    simp [f, rest]
  have dep : ∃ x, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x := by
    let x : Fin (n + 1) → Bool := fun _ => false
    refine ⟨x, ?_⟩
    rw [hlast]
    change xor true (g (fun _ => false)) ≠ xor false (g (fun _ => false))
    cases g (fun _ => false) <;> decide
  have nc : ∀ b : Bool, ∃ y y', f (Fin.snoc y b) ≠ f (Fin.snoc y' b) := by
    intro b
    obtain ⟨y, y', hy⟩ := hne
    refine ⟨y, y', ?_⟩
    cases b <;> simpa [f] using hy
  obtain ⟨b, t, ht, C, hok, hsize, heval⟩ := gate_elim_two n f (s + 2) dep nc hc
  have hlen : C.size ≤ s := by omega
  cases b
  · exact Or.inl ⟨C, hok, hlen, fun y => by simpa [f] using heval y⟩
  · exact Or.inr ⟨C, hok, hlen, fun y => by simpa [f] using heval y⟩

end PEqualNP.Outside.L_meta_604
