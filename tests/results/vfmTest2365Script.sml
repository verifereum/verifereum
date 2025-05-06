open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2365Theory;
val () = new_theory "vfmTest2365";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2365") $ get_result_defs "vfmTestDefs2365";
val () = export_theory_no_docs ();
