open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0497Theory;
val () = new_theory "vfmTest0497";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0497") $ get_result_defs "vfmTestDefs0497";
val () = export_theory_no_docs ();
