open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2284Theory;
val () = new_theory "vfmTest2284";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2284") $ get_result_defs "vfmTestDefs2284";
val () = export_theory_no_docs ();
