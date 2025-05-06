open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2873Theory;
val () = new_theory "vfmTest2873";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2873") $ get_result_defs "vfmTestDefs2873";
val () = export_theory_no_docs ();
