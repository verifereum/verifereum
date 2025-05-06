open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2326Theory;
val () = new_theory "vfmTest2326";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2326") $ get_result_defs "vfmTestDefs2326";
val () = export_theory_no_docs ();
