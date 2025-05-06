open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1976Theory;
val () = new_theory "vfmTest1976";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1976") $ get_result_defs "vfmTestDefs1976";
val () = export_theory_no_docs ();
