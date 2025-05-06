open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2626Theory;
val () = new_theory "vfmTest2626";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2626") $ get_result_defs "vfmTestDefs2626";
val () = export_theory_no_docs ();
