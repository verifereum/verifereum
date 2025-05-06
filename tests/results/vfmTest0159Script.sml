open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0159Theory;
val () = new_theory "vfmTest0159";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0159") $ get_result_defs "vfmTestDefs0159";
val () = export_theory_no_docs ();
