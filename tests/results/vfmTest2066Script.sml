open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2066Theory;
val () = new_theory "vfmTest2066";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2066") $ get_result_defs "vfmTestDefs2066";
val () = export_theory_no_docs ();
