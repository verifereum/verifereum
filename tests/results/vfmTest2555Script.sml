open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2555Theory;
val () = new_theory "vfmTest2555";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2555") $ get_result_defs "vfmTestDefs2555";
val () = export_theory_no_docs ();
