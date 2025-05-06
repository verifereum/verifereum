open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2589Theory;
val () = new_theory "vfmTest2589";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2589") $ get_result_defs "vfmTestDefs2589";
val () = export_theory_no_docs ();
