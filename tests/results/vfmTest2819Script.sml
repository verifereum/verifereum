open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2819Theory;
val () = new_theory "vfmTest2819";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2819") $ get_result_defs "vfmTestDefs2819";
val () = export_theory_no_docs ();
