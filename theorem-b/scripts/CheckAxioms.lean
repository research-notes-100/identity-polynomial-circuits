/-
The axiom gate: every constant declared in a `TheoremB` module — theorems, definitions, private
and auxiliary declarations alike — must depend only on propext, Classical.choice and Quot.sound.

    lake build && lake env lean scripts/CheckAxioms.lean

It reads the compiled environment, not the source text, so no declaration can be missed by a
pattern, and it exits with an error if any constant depends on another axiom (`sorryAx` included)
or if a file under `TheoremB/` is not imported below. `scripts/PrintAxioms.lean` lists the main
theorems by name for a reader; this file is the check.
-/
import TheoremB.Defs
import TheoremB.Corollaries
import TheoremB.PTRank
import TheoremB.CharP
import TheoremB.CharPGrowth
import TheoremB.Rectangular
import TheoremB.Sanity

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let isOurs (m : Name) : Bool := (`TheoremB).isPrefixOf m && m != `TheoremB
  -- Every file under TheoremB/ must be one of the imported modules.
  let imported := env.header.moduleNames.filter isOurs
  let files ← System.FilePath.walkDir "TheoremB"
  for f in files do
    if f.extension == some "lean" then
      let comps := (f.withExtension "").components
      let m := comps.foldl (fun n c => Name.str n c) Name.anonymous
      unless imported.contains m do
        throwError m!"{f} is not imported by scripts/CheckAxioms.lean, so it would go unchecked"
  -- Every constant of those modules.
  let mut checked : Nat := 0
  let mut bad : Array MessageData := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if isOurs m then
      for n in env.header.moduleData[i]!.constNames do
        let axs ← collectAxioms n
        checked := checked + 1
        let extra := axs.toList.filter (fun a => !allowed.contains a)
        unless extra.isEmpty do
          bad := bad.push m!"{n} ({m}) depends on {extra}"
  if checked == 0 then
    throwError "no TheoremB constants found"
  unless bad.isEmpty do
    throwError m!"{bad.size} constants depend on axioms beyond propext, Classical.choice, Quot.sound:\n{MessageData.joinSep bad.toList "\n"}"
  logInfo m!"{checked} constants in {imported.size} TheoremB modules; all depend only on propext, Classical.choice and Quot.sound"
