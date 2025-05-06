open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2741Theory;
val () = new_theory "vfmTest2741";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2741") $ get_result_defs "vfmTestDefs2741";
val () = export_theory_no_docs ();
