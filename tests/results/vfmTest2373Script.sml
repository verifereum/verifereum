open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2373Theory;
val () = new_theory "vfmTest2373";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2373") $ get_result_defs "vfmTestDefs2373";
val () = export_theory_no_docs ();
