(* Dummy theory that depends on all the targets in the project,
   for ease of "building everything" *)
open HolKernel
  contractABITheory contractABISyntax
  vfmDomainCollectionTheory
  vfmTestRunTheory vfmTestDefLib vfmTestResultLib
  vfmProgTheory wrappedEtherTheory

val () = new_theory "verifereum";

val () = export_theory();
