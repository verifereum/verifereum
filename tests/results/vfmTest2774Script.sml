open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2774Theory;
val () = new_theory "vfmTest2774";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2774") $ get_result_defs "vfmTestDefs2774";
val () = export_theory_no_docs ();
