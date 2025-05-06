open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1496Theory;
val () = new_theory "vfmTest1496";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1496") $ get_result_defs "vfmTestDefs1496";
val () = export_theory_no_docs ();
