(* Dummy theory that depends on all the targets in the project,
   for ease of "building everything" *)
open HolKernel
  contractABITheory contractABISyntax
  vfmDomainCollectionTheory
  vfmTestRunTheory vfmTestDefLib vfmTestResultLib
  vfmSettlementTheory vfmAccountingTheory vfmHistoryRingTheory
  vfmOriginalStateTheory vfmOriginalAccountsTheory
  vfmContextLengthTheory vfmAccountFrameTheory vfmAccountDeletionTheory
  vfmProgTheory vfmProgCallTheory wrappedEtherTheory wrappedEtherNameTheory
  wrappedEtherTransferTheory wrappedEtherBranchesTheory wrappedEtherGettersTheory
  (* Checked counterexamples, evidence for the state-gas hypotheses this
     series added to published theorems: each one is a witness that its
     namesake is false without the hypothesis its comment points at.
     Nothing depends on them, so without these lines the root build would
     never compile them. *)
  vfmProgCounterexampleTheory vfmProgChargedRevertProbeTheory
  vfmPopGasProbeTheory vfmGasStackProbeTheory vfmSstoreGasProbeTheory
  vfmCallDrainProbeTheory

val () = new_theory "verifereum";

val () = export_theory();
