open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1552Theory;
val () = new_theory "vfmTest1552";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1552") $ get_result_defs "vfmTestDefs1552";
val () = export_theory_no_docs ();
