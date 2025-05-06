open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1647Theory;
val () = new_theory "vfmTest1647";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1647") $ get_result_defs "vfmTestDefs1647";
val () = export_theory_no_docs ();
