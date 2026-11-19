(* Dummy theory that depends on all the targets in the project,
   for ease of "building everything" *)
open HolKernel
  contractABITheory contractABISyntax
  vfmDomainCollectionTheory vfmTotalBalanceTheory vfmCalldataBoundTheory
  vfmReturndataBoundTheory vfmToDeleteTheory vfmDeletionQueueTheory
  vfmTestRunTheory vfmTestDefLib vfmTestResultLib vfmChainIdTheory
  vfmSettlementTheory vfmAccountingTheory vfmHistoryRingTheory
  vfmCreateCollisionTheory vfmDepositLogTheory vfmSystemTransactionTheory
  vfmSystemContractsTheory
  vfmOriginalStateTheory vfmOriginalAccountsTheory
  vfmRunFrameTheory vfmContextLengthTheory vfmAccountFrameTheory vfmAccountDeletionTheory
  vfmProgTheory vfmProgCallTheory

val () = new_theory "verifereum";

val () = export_theory();
