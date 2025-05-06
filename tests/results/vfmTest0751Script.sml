open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0751Theory;
val () = new_theory "vfmTest0751";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0751") $ get_result_defs "vfmTestDefs0751";
val () = export_theory_no_docs ();
