open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1352Theory;
val () = new_theory "vfmTest1352";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1352") $ get_result_defs "vfmTestDefs1352";
val () = export_theory_no_docs ();
