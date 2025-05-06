open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1133Theory;
val () = new_theory "vfmTest1133";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1133") $ get_result_defs "vfmTestDefs1133";
val () = export_theory_no_docs ();
