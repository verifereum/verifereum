open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1907Theory;
val () = new_theory "vfmTest1907";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1907") $ get_result_defs "vfmTestDefs1907";
val () = export_theory_no_docs ();
