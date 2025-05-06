open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1423Theory;
val () = new_theory "vfmTest1423";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1423") $ get_result_defs "vfmTestDefs1423";
val () = export_theory_no_docs ();
