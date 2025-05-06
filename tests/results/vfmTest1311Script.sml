open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1311Theory;
val () = new_theory "vfmTest1311";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1311") $ get_result_defs "vfmTestDefs1311";
val () = export_theory_no_docs ();
