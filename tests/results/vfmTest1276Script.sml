open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1276Theory;
val () = new_theory "vfmTest1276";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1276") $ get_result_defs "vfmTestDefs1276";
val () = export_theory_no_docs ();
