open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2394Theory;
val () = new_theory "vfmTest2394";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2394") $ get_result_defs "vfmTestDefs2394";
val () = export_theory_no_docs ();
