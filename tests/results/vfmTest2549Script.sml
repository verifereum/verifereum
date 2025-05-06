open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2549Theory;
val () = new_theory "vfmTest2549";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2549") $ get_result_defs "vfmTestDefs2549";
val () = export_theory_no_docs ();
