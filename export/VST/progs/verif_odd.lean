/-
  Port of VST's `progs/verif_odd.v`: `odd` of `vst/progs/odd.c`, compiled
  separately from `even` (`vst/progs/even.c`, `verif_even.lean`).

  As in VST (`all_funcs_correct`, with `even` an external function whose
  specification is in `Gprog`), the theorem assumes that the global `even`
  meets `even_spec`; the body proof is the shared `body_ok` of
  `verif_evenodd.lean`.
-/
import VST.progs.odd
import VST.progs.verif_even
open CC CC.Sep CC.HProp
open VST.Verif.Evenodd VST.Verif.Even

namespace VST.Verif.Odd
open _root_.Odd

/-- **`odd` satisfies `odd_spec`** (VST's `body_odd`), given that `even`
    satisfies `even_spec`. -/
theorem odd_satisfies (ge : CGenv) (heven : MeetsSpec ge _even true) (n : Nat)
    (hn : (n : _root_.Int) < 4294967296) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_odd) (eoSpec false n)
      [.Vint (Integers.Int.repr n)] := by
  obtain ⟨be, fde, hsym, hfind, hty, hspec⟩ := heven
  exact body_ok ge f_odd false _even be fde hsym hfind hty rfl rfl rfl rfl rfl n hn
    (fun _ => hspec (n - 1) (by omega))

end VST.Verif.Odd
