/-
  The `ccomp` executable: the command-line driver of `driver/Driver.ml`
  (`CCLib.driver.Driver`) for the AArch64 target (`Driver.aarch64Target`).

  Without a configuration file (`compcert.ini`, option `-conf`, variable
  `COMPCERT_CONFIG`), the configuration is `Driver.aarch64_linux`, the
  parameters written by `./configure aarch64-linux`.  On a host that is not
  AArch64 Linux, use `-S` (assembly only) or a configuration file naming a
  cross toolchain.  `ccomp -interp file.c` runs the reference interpreter
  (`CCLib.driver.Interp`) on the host: it executes the CompCert C semantics
  (options `-quiet`, `-trace`, `-random`, `-all`).
-/
import CCLib.driver.Driver

def main (args : List String) : IO UInt32 :=
  CC.Driver.main CC.Driver.aarch64Target "ccomp" args CC.Driver.aarch64_linux
