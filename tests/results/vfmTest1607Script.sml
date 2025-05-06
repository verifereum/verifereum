open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1607Theory;
val () = new_theory "vfmTest1607";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1607") $ get_result_defs "vfmTestDefs1607";
val () = export_theory_no_docs ();
