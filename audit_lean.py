"""Check imported project theorems for unexpected axiom dependencies."""

from pathlib import Path
import re
import subprocess


def main():
    repo = Path(__file__).resolve().parent
    listed = subprocess.check_output(["git","ls-files","-z","--","*.lean"],cwd=repo)
    files = [name.decode("utf-8") for name in listed.split(b"\0") if name]
    modules = [path[:-5].replace("/",".") for path in files]
    if not modules or not all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*",m) for m in modules):
        raise ValueError("expected tracked Lean modules with ordinary names")
    imports = "\n".join(f"import {m}" for m in modules)
    names = ", ".join("`"+m for m in modules)
    source = f"""import Lean
{imports}
open Lean Elab Command in
run_cmd do
  let targets : List Name := [{names}]
  let allowed : List Name := [`propext, `Quot.sound, `Classical.choice]
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if let .thmInfo _ := info then
      if let some idx := env.getModuleIdxFor? name then
        if targets.contains env.header.moduleNames[idx.toNat]! then
          checked := checked + 1
          for ax in (← collectAxioms name) do
            unless allowed.contains ax do
              throwError m!"unexpected axiom {{ax}} in {{name}}"
  if checked == 0 then throwError "no project theorems found"
  logInfo m!"audited {{checked}} project theorem declarations"
"""
    completed = subprocess.run(["lake","env","lean","--stdin"],input=source,encoding="utf-8",cwd=repo)
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
