open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1518Theory;
val () = new_theory "vfmTest1518";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1518") $ get_result_defs "vfmTestDefs1518";
val () = export_theory_no_docs ();
