open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2695Theory;
val () = new_theory "vfmTest2695";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2695") $ get_result_defs "vfmTestDefs2695";
val () = export_theory_no_docs ();
