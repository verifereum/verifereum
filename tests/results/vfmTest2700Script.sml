open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2700Theory;
val () = new_theory "vfmTest2700";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2700") $ get_result_defs "vfmTestDefs2700";
val () = export_theory_no_docs ();
