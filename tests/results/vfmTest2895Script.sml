open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2895Theory;
val () = new_theory "vfmTest2895";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2895") $ get_result_defs "vfmTestDefs2895";
val () = export_theory_no_docs ();
