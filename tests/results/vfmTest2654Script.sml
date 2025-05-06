open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2654Theory;
val () = new_theory "vfmTest2654";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2654") $ get_result_defs "vfmTestDefs2654";
val () = export_theory_no_docs ();
