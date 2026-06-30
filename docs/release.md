# Release process

Verifereum releases are GitHub Releases. Each release should include a
prebuilt holbuild archive for the project default roots.

## Maintainer checklist

1. Choose the release version and update `holproject.toml` if needed.
2. Ensure the `holbuild` workflow is green for the commit being released. It
   should have uploaded an artefact named `verifereum-hbx-<commit-sha>`.
3. Create a tag for that commit, using a name such as `v0.1.5`.
4. If needed, run the `holbuild` workflow manually for the tag and wait for it
   to upload `verifereum-hbx-<commit-sha>`.
5. Create and publish the GitHub Release for the tag.
6. Publishing the GitHub Release starts `.github/workflows/release.yml`, which
   promotes the CI artefact to release assets:

   ```text
   verifereum.hbx
   verifereum.hbx.json
   verifereum.hbx.sha256
   ```

The CI artefact is retained for 90 days. If the release workflow needs to be
rerun after the artefact has expired, run the `holbuild` workflow manually for
the release tag first, then rerun `Release artefacts` with `workflow_dispatch`
and provide the existing release tag. The release workflow does not rebuild the
archive; it downloads the matching `holbuild` workflow artefact for the release
commit and uploads those exact files to the GitHub Release.

## Manual archive build

The CI artefact is the preferred release source. To build the same archive
locally or from another CI system, use holbuild v0.8.1 or newer:

```bash
holbuild buildhol
holbuild -j"$(nproc)" build
holbuild export \
  -o verifereum.hbx \
  --metadata-out verifereum.hbx.json
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
holbuild build
```
