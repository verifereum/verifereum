open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0088Theory;
val () = new_theory "vfmTest0088";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0088") $ get_result_defs "vfmTestDefs0088";
val () = export_theory_no_docs ();
