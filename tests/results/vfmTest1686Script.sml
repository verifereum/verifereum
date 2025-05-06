open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1686Theory;
val () = new_theory "vfmTest1686";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1686") $ get_result_defs "vfmTestDefs1686";
val () = export_theory_no_docs ();
