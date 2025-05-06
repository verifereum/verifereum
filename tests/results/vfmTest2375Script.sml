open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2375Theory;
val () = new_theory "vfmTest2375";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2375") $ get_result_defs "vfmTestDefs2375";
val () = export_theory_no_docs ();
