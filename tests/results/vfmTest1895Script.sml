open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1895Theory;
val () = new_theory "vfmTest1895";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1895") $ get_result_defs "vfmTestDefs1895";
val () = export_theory_no_docs ();
