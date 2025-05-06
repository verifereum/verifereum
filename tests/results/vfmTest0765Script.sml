open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0765Theory;
val () = new_theory "vfmTest0765";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0765") $ get_result_defs "vfmTestDefs0765";
val () = export_theory_no_docs ();
