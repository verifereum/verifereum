(* Dummy theory that depends on all the targets in the project,
   for ease of "building everything" *)
open HolKernel
  contractABITheory contractABISyntax
  vfmDomainCollectionTheory
  vfmTestRunTheory vfmTestDefLib vfmTestResultLib
  vfmSettlementTheory vfmAccountingTheory vfmHistoryRingTheory
  vfmCreateCollisionTheory
  vfmOriginalStateTheory vfmOriginalAccountsTheory
  vfmContextLengthTheory vfmAccountFrameTheory vfmAccountDeletionTheory
  vfmProgTheory vfmProgCallTheory wrappedEtherTheory wrappedEtherNameTheory
  wrappedEtherTransferTheory wrappedEtherBranchesTheory wrappedEtherGettersTheory

val () = new_theory "verifereum";

val () = export_theory();
