open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1942Theory;
val () = new_theory "vfmTest1942";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1942") $ get_result_defs "vfmTestDefs1942";
val () = export_theory_no_docs ();
