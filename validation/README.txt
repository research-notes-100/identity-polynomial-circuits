Verification records

release/      The ID-MM project at the repository root, checked by scripts/validate.py:
  validation.json   SHA-256 of every Lean source and pin file; command, exit code, Eastern timestamps and
                    log hash of each stage.
  build.log         the full lake build.
  axioms.log, axioms_every_char.log
                    signatures and axiom lists of the top-level theorems in the two import closures
                    (IDMM/FinalAudit.lean: the OpenAI route; IDMM/FinalAuditEveryChar.lean: Theorem 1.1).
  kernel.log, kernel_every_char.log
                    lake env leanchecker --fresh on IDMM.FinalAudit and IDMM.FinalAuditEveryChar.
  audit.json        scripts/audit.py on the record.
  The two closures are separate because Matmul (Zhou and Wang) and OAI.LinearAlgebra.MatrixMultiplication.Main
  declare clashing names.

theorem-b/    The theorem-b project: lake build, scripts/CheckAxioms.lean (every constant of the seven
              TheoremB modules), scripts/PrintAxioms.lean, and lake env leanchecker on each module, both in
              place and with --fresh. validation.json records source hashes, commands, exit codes and log hashes.

provenance.json      upstream hashes of OpenAI's and Zhou and Wang's files, and the one documented Matmul edit.
paulicubes-port.patch  the edits that ported PauliCubes from Lean 4.33.1 to 4.34.1.

Paths in the logs are written as <repo> and ~.

Reproduce:
  python3 scripts/validate.py --out validation/release
  python3 scripts/audit.py
