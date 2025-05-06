open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1266Theory;
val () = new_theory "vfmTest1266";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1266") $ get_result_defs "vfmTestDefs1266";
val () = export_theory_no_docs ();
