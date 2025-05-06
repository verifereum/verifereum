open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2213Theory;
val () = new_theory "vfmTest2213";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2213") $ get_result_defs "vfmTestDefs2213";
val () = export_theory_no_docs ();
