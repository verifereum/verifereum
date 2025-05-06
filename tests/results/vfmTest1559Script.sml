open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1559Theory;
val () = new_theory "vfmTest1559";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1559") $ get_result_defs "vfmTestDefs1559";
val () = export_theory_no_docs ();
