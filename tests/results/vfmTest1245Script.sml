open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1245Theory;
val () = new_theory "vfmTest1245";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1245") $ get_result_defs "vfmTestDefs1245";
val () = export_theory_no_docs ();
