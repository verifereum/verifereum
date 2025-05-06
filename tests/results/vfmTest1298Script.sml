open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1298Theory;
val () = new_theory "vfmTest1298";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1298") $ get_result_defs "vfmTestDefs1298";
val () = export_theory_no_docs ();
