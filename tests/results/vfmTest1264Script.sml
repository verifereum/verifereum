open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1264Theory;
val () = new_theory "vfmTest1264";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1264") $ get_result_defs "vfmTestDefs1264";
val () = export_theory_no_docs ();
