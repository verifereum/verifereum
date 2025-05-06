open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1139Theory;
val () = new_theory "vfmTest1139";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1139") $ get_result_defs "vfmTestDefs1139";
val () = export_theory_no_docs ();
