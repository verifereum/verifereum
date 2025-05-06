open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2179Theory;
val () = new_theory "vfmTest2179";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2179") $ get_result_defs "vfmTestDefs2179";
val () = export_theory_no_docs ();
