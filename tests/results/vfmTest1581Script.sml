open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1581Theory;
val () = new_theory "vfmTest1581";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1581") $ get_result_defs "vfmTestDefs1581";
val () = export_theory_no_docs ();
