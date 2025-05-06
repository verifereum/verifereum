open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2523Theory;
val () = new_theory "vfmTest2523";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2523") $ get_result_defs "vfmTestDefs2523";
val () = export_theory_no_docs ();
