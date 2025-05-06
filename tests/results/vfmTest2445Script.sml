open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2445Theory;
val () = new_theory "vfmTest2445";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2445") $ get_result_defs "vfmTestDefs2445";
val () = export_theory_no_docs ();
