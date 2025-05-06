open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1503Theory;
val () = new_theory "vfmTest1503";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1503") $ get_result_defs "vfmTestDefs1503";
val () = export_theory_no_docs ();
