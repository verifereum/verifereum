open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2039Theory;
val () = new_theory "vfmTest2039";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2039") $ get_result_defs "vfmTestDefs2039";
val () = export_theory_no_docs ();
