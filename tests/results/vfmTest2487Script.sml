open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2487Theory;
val () = new_theory "vfmTest2487";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2487") $ get_result_defs "vfmTestDefs2487";
val () = export_theory_no_docs ();
