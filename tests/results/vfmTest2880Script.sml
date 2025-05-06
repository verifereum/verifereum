open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2880Theory;
val () = new_theory "vfmTest2880";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2880") $ get_result_defs "vfmTestDefs2880";
val () = export_theory_no_docs ();
