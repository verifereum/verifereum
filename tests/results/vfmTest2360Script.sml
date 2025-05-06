open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2360Theory;
val () = new_theory "vfmTest2360";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2360") $ get_result_defs "vfmTestDefs2360";
val () = export_theory_no_docs ();
