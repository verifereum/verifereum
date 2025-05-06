open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2501Theory;
val () = new_theory "vfmTest2501";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2501") $ get_result_defs "vfmTestDefs2501";
val () = export_theory_no_docs ();
