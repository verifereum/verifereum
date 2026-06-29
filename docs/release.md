# Release process

Verifereum releases are GitHub Releases. Each release should include a
prebuilt holbuild archive for the top-level `verifereum` target.

## Maintainer checklist

1. Choose the release version and update `holproject.toml` if needed.
2. Ensure CI is green for the commit being released.
3. Create a tag and GitHub Release for that commit, using matching names such as
   `v0.1.5`.
4. Publishing the GitHub Release starts `.github/workflows/release.yml`, which
   uploads:

   ```text
   verifereum.hbx
   verifereum.hbx.json
   verifereum.hbx.sha256
   ```

If the release workflow needs to be rerun, use the `Release artifacts` workflow
with `workflow_dispatch` and provide the existing release tag.

## Manual archive build

The workflow is the preferred release path. To build the same archive locally
or from another CI system, use holbuild v0.8.1 or newer:

```bash
holbuild buildhol
holbuild -j"$(nproc)" build verifereum
holbuild export \
  -o verifereum.hbx \
  --metadata-out verifereum.hbx.json \
  verifereum
sha256sum verifereum.hbx > verifereum.hbx.sha256
```

Upload all three files to the GitHub Release:

```bash
gh release upload vX.Y.Z \
  verifereum.hbx \
  verifereum.hbx.json \
  verifereum.hbx.sha256
```

## Consuming a release archive

```bash
gh release download vX.Y.Z \
  -p verifereum.hbx \
  -p verifereum.hbx.json \
  -p verifereum.hbx.sha256
sha256sum -c verifereum.hbx.sha256
holbuild import verifereum.hbx
holbuild build verifereum
```
