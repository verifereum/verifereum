open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1381Theory;
val () = new_theory "vfmTest1381";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1381") $ get_result_defs "vfmTestDefs1381";
val () = export_theory_no_docs ();
