open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2254Theory;
val () = new_theory "vfmTest2254";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2254") $ get_result_defs "vfmTestDefs2254";
val () = export_theory_no_docs ();
