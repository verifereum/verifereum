open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2556Theory;
val () = new_theory "vfmTest2556";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2556") $ get_result_defs "vfmTestDefs2556";
val () = export_theory_no_docs ();
