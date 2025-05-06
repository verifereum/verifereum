open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1548Theory;
val () = new_theory "vfmTest1548";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1548") $ get_result_defs "vfmTestDefs1548";
val () = export_theory_no_docs ();
