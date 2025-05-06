open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0149Theory;
val () = new_theory "vfmTest0149";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0149") $ get_result_defs "vfmTestDefs0149";
val () = export_theory_no_docs ();
