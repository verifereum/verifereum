open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2048Theory;
val () = new_theory "vfmTest2048";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2048") $ get_result_defs "vfmTestDefs2048";
val () = export_theory_no_docs ();
