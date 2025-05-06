open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1414Theory;
val () = new_theory "vfmTest1414";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1414") $ get_result_defs "vfmTestDefs1414";
val () = export_theory_no_docs ();
