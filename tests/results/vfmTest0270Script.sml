open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0270Theory;
val () = new_theory "vfmTest0270";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0270") $ get_result_defs "vfmTestDefs0270";
val () = export_theory_no_docs ();
