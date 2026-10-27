(* Dummy theory that depends on all the targets in the project,
   for ease of "building everything" *)
open HolKernel
  contractABITheory contractABISyntax
  vfmDomainCollectionTheory
  vfmTestRunTheory vfmTestDefLib vfmTestResultLib
  vfmSettlementTheory vfmAccountingTheory
  vfmOriginalStateTheory vfmOriginalAccountsTheory
  vfmContextLengthTheory vfmAccountFrameTheory vfmAccountDeletionTheory
  vfmProgTheory wrappedEtherTheory
  (* Checked counterexamples kept as evidence for the EIP-8037 statement
     shapes.  Nothing depends on them, so without this line the root build
     would never compile them. *)
  vfmProgCounterexampleTheory
  vfmPopGasProbeTheory vfmGasStackProbeTheory
  vfmCallDrainProbeTheory vfmSstoreGasProbeTheory

val () = new_theory "verifereum";

val () = export_theory();
