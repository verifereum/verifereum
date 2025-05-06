open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2751Theory;
val () = new_theory "vfmTest2751";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2751") $ get_result_defs "vfmTestDefs2751";
val () = export_theory_no_docs ();
