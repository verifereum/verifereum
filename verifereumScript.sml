(* Dummy theory that depends on all the targets in the project,
   for ease of "building everything" *)
open HolKernel
  contractABITheory contractABISyntax
  vfmDomainCollectionTheory
  vfmTestRunTheory vfmTestDefLib vfmTestResultLib vfmChainIdTheory
  vfmSettlementTheory vfmAccountingTheory vfmHistoryRingTheory
  vfmOriginalStateTheory vfmOriginalAccountsTheory
  vfmContextLengthTheory vfmAccountFrameTheory vfmAccountDeletionTheory
  vfmProgTheory vfmProgCallTheory

val () = new_theory "verifereum";

val () = export_theory();
