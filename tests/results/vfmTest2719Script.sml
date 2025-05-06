open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2719Theory;
val () = new_theory "vfmTest2719";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2719") $ get_result_defs "vfmTestDefs2719";
val () = export_theory_no_docs ();
