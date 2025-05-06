open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1213Theory;
val () = new_theory "vfmTest1213";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1213") $ get_result_defs "vfmTestDefs1213";
val () = export_theory_no_docs ();
