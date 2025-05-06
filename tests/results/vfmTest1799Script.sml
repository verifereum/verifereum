open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1799Theory;
val () = new_theory "vfmTest1799";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1799") $ get_result_defs "vfmTestDefs1799";
val () = export_theory_no_docs ();
