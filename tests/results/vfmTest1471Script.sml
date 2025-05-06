open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1471Theory;
val () = new_theory "vfmTest1471";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1471") $ get_result_defs "vfmTestDefs1471";
val () = export_theory_no_docs ();
