open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0407Theory;
val () = new_theory "vfmTest0407";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0407") $ get_result_defs "vfmTestDefs0407";
val () = export_theory_no_docs ();
