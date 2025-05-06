open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0005Theory;
val () = new_theory "vfmTest0005";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0005") $ get_result_defs "vfmTestDefs0005";
val () = export_theory_no_docs ();
