open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1189Theory;
val () = new_theory "vfmTest1189";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1189") $ get_result_defs "vfmTestDefs1189";
val () = export_theory_no_docs ();
