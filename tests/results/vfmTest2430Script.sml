open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2430Theory;
val () = new_theory "vfmTest2430";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2430") $ get_result_defs "vfmTestDefs2430";
val () = export_theory_no_docs ();
