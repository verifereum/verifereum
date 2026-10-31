# STATE_seq58_progcall_port
Updated: 2026-10-31

## Cursor
- component: C1.7
- status: in_progress
- active_file: prog/vfmProgCallScript.sml
- next_action: Run final holbuild target, then reclose C1.7 with final-build evidence plus commit 736af961 and clean status evidence TO_seq58_progcall_port-20261031T211644Z_m1905_t001. Review rejected E0063 solely because commit/clean-status/postcommit-build evidence was not yet supplied. Commit is now done with required trailers; all five exports proved. After accepted review commit generated dossier/memory changes, ensure clean status and final build, and propose completion through available end-session mechanism.
- expected_goal_shape: No HOL goals remain; vfmProgCallTheory should build or be current. Only completion evidence/review and final clean repository bookkeeping remain.
- verify_with: holbuild(targets=["vfmProgCallTheory"], timeout=1800); git status --porcelain

## If This Fails
- If ordinary build failure inspect exact goal; do not change statements. If review requests evidence supply it. Do not redo proofs or redesign PLAN for bookkeeping.

## Do Not Retry
- Expand final = semantic context while simplifying post/frame: Defeats supplied projections and leaves parsed-code conjunct ahead of existential witnesses.
  - evidence: tool_output:TO_seq58_progcall_port-20261031T211644Z_m1852_t001
  - evidence: episode:E0062

## Reflection
### Tunnel Vision Check
- Fresh expert should first verify final target and git cleanliness, not reopen now-proved exports.
- No unexplored mathematical alternative is needed: the protected boundary was sufficient. Remaining obstacle is completion evidence sequencing.
- PLAN decomposition is complete; C1.7 is evidence repair only, not proof repair.

### What Went Wrong
- Legacy post simp expanded final's implementation equality before using final.msgParams; residual CODE_POOL lookup conjunct made qexistsl_tac fail 'not an exists'. Removing final = _ from post/frame contexts permits supplied projections to fire.
- Final audit closure was premature: strategist requires final commit identifier, clean git status and postcommit build before accepting C1.7.

### Ignored Signals
- Macro failure showed only outer goal; inline inspection exposed residual code conjunct immediately.
- Successful target build does not itself satisfy commit/clean-status evidence requirements.

### Strategy Adjustments
- Shared post/frame consumers remove final implementation equality, use projection interface, keep merged opaque with IgnAsm during separation normalization, then discharge cond with its equation.
- Five public exports have a direct Tag.isDisk/Tag.isEmpty assertion in source, checked by successful build; installation emits Theory.dat not Theory.txt.

### Oracle Feedback
- E0062 C1.6.2 accepted and committed da33f8ed; both export formulas unchanged this session.
- E0063 review rejected only for missing final commit/status/build sequencing. Final audit/source commit now 736af961; clean porcelain checked immediately afterward. Need new final build and reclosure.

## Evidence Pointers
- episode:E0062 - both shared export applications proved and reviewed
- episode:E0063 - final statement/prohibited-proof/path audit, closure requires replacement evidence
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1894_t001 - successful full target with five-export kernel tag assertion
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1901_t001 - exact rejected review evidence requirements
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1903_t001 - final commit 736af961 and required trailers
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1905_t001 - postcommit clean status
- source:prog/AUDIT_seq58_call_safety.md - final contract audit
