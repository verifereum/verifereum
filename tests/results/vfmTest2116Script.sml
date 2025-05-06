open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2116Theory;
val () = new_theory "vfmTest2116";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2116") $ get_result_defs "vfmTestDefs2116";
val () = export_theory_no_docs ();
