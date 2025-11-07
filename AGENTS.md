# Agent Guidelines

- Prefer `simp at h` instead of `simpa using h`.
- Build with mathlib using `lake`. If you need to invoke `lean` directly, prefix the command with `lake env` first.
- When adding Lean files, remember imports use `.` separators (e.g., `import A.B`) rather than `/`.
