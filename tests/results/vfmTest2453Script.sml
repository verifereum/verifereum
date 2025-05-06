open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2453Theory;
val () = new_theory "vfmTest2453";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2453") $ get_result_defs "vfmTestDefs2453";
val () = export_theory_no_docs ();
