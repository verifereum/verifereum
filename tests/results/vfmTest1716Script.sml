open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1716Theory;
val () = new_theory "vfmTest1716";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1716") $ get_result_defs "vfmTestDefs1716";
val () = export_theory_no_docs ();
