open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1283Theory;
val () = new_theory "vfmTest1283";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1283") $ get_result_defs "vfmTestDefs1283";
val () = export_theory_no_docs ();
