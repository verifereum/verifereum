open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1640Theory;
val () = new_theory "vfmTest1640";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1640") $ get_result_defs "vfmTestDefs1640";
val () = export_theory_no_docs ();
