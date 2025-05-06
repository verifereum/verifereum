open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1347Theory;
val () = new_theory "vfmTest1347";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1347") $ get_result_defs "vfmTestDefs1347";
val () = export_theory_no_docs ();
