open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1363Theory;
val () = new_theory "vfmTest1363";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1363") $ get_result_defs "vfmTestDefs1363";
val () = export_theory_no_docs ();
