open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1361Theory;
val () = new_theory "vfmTest1361";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1361") $ get_result_defs "vfmTestDefs1361";
val () = export_theory_no_docs ();
