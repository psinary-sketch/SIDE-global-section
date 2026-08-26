#!/bin/sh
# b193 -- the Mathlib LEAN_PATH, assembled once and reused.
# ### Mathlib's own toolchain is v4.29.0 (its lean-toolchain, read at content);
# ### the default 4.29.1 gives "incompatible header". ### THE TOOLCHAIN IS PART OF THE PATH.
M="D:/MY-DOwnloads/mathlib4"
P="$M/.lake/build/lib/lean"
for d in "$M"/.lake/packages/*/.lake/build/lib/lean; do
  P="$P;$d"
done
export LEAN_PATH="$P"
exec elan run leanprover/lean4:v4.29.0 lean "$@"
