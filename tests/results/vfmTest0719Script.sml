open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0719Theory;
val () = new_theory "vfmTest0719";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0719") $ get_result_defs "vfmTestDefs0719";
val () = export_theory_no_docs ();
