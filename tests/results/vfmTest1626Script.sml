open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1626Theory;
val () = new_theory "vfmTest1626";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1626") $ get_result_defs "vfmTestDefs1626";
val () = export_theory_no_docs ();
