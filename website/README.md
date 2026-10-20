# Website

Source of <https://verifereum.org>. `make` renders the markdown with
[pandoc](https://pandoc.org), and `make deploy DEPLOY_DEST=user@host:/path`
uploads the site with rsync.

The deployed site holds:

- `index.html` and `contribute.html`, from `index.md` and `contribute.md`
  here;
- `index.css` and the two `verifereum-logo-*.svg` files, which the pages
  reference relatively;
- `talks/`, a copy of the repository's `talks/` directory, which `index.md`
  links to as `talks/<deck>/`;
- `table.html`, with `table.css` and `table.js`, the conformance test
  results. `tests/runtests.exe` writes `table.html` into `tests/results/`,
  next to the other two, and they are uploaded after a test run, not by
  `make deploy`, which leaves them alone.

The server's content security policy allows no inline styles or scripts, so
all styling goes in `index.css`.
