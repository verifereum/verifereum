open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1941Theory;
val () = new_theory "vfmTest1941";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1941") $ get_result_defs "vfmTestDefs1941";
val () = export_theory_no_docs ();
