import Lake
open Lake DSL

-- Core Lean only (no Mathlib): the agent's proofs must check against exactly this toolchain.
package «glimmer-verify» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib GlimmerVerify where
