open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2285Theory;
val () = new_theory "vfmTest2285";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2285") $ get_result_defs "vfmTestDefs2285";
val () = export_theory_no_docs ();
