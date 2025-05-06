open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1617Theory;
val () = new_theory "vfmTest1617";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1617") $ get_result_defs "vfmTestDefs1617";
val () = export_theory_no_docs ();
