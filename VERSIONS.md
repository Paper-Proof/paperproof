# Paperproof versions

To determine what Paperproof version you need, do the following:

1. Look at `lean-toolchain` of your project.  
  Suppose it says your lean version is `v4.25.0`.
2. Consult the table below. It says that for Lean version `v4.25.0`, you need  
    1) Paperproof library with git tag `v2.7.0`
    2) VSCode extension with version `v2.7.0`
3. 
    In your `lakefile.toml`, write:
    ```toml
    [[require]]
    name = "Paperproof"
    git = "https://github.com/Paper-Proof/paperproof.git"
    rev = "v2.7.0"
    subDir = "lean"
    ```
4. In your VSCode editor:
    ```
    right-click "Paperproof" in the Extensions panel →
    click "Install Specific Version..." →
    choose v2.7.0
    ```

| Lean version (min) | Lean version (max) | Git tag | VSCode Extension |
|---|---|---|---|
| **v4.27.0** | **v4.29.0** | `main` | `v2.7.0` |
| needs testing | **v4.25.0** | `v2.7.0` | `v2.7.0` |
| needs testing | **v4.12.0** | `v2.0.0` | `v2.0.0` |
| needs testing | **v4.0.0** | `v1.0.0` | `v1.0.0` |

