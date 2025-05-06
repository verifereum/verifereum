open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1231Theory;
val () = new_theory "vfmTest1231";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1231") $ get_result_defs "vfmTestDefs1231";
val () = export_theory_no_docs ();
