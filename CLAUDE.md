# Gaussian Field Project Guidelines

## Agent Rules
- **NEVER let 2 agents work on the same file simultaneously.** This causes file conflicts where one agent's writes overwrite the other's work, leading to lost proofs. Always assign each file to at most one agent at a time.
- **Protocol for parallel work on the same file:**
  1. Only ONE agent works in the main tree per file.
  2. Additional agents MUST use `isolation: "worktree"` to get their own copy.
  3. After agents finish, merge worktree changes sequentially (not simultaneously).
  4. Before launching an agent, check what files it will modify and ensure no other main-tree agent is editing them.

## Build
- `lake build` from project root
- Individual modules: `lake build HeatKernel.PositionKernel`
- Long build times (~30-60s per module)
