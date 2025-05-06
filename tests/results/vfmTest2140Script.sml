open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2140Theory;
val () = new_theory "vfmTest2140";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2140") $ get_result_defs "vfmTestDefs2140";
val () = export_theory_no_docs ();
