(* Dummy theory that depends on all the targets in the project,
   for ease of "building everything" *)
open HolKernel
  contractABITheory contractABISyntax
  vfmDomainCollectionTheory
  vfmTestRunTheory vfmTestDefLib vfmTestResultLib
  (* TODO: add things in prog/ once they are fixed *)

val () = new_theory "verifereum";

val () = export_theory();
