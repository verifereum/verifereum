open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1179Theory;
val () = new_theory "vfmTest1179";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1179") $ get_result_defs "vfmTestDefs1179";
val () = export_theory_no_docs ();
