open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2602Theory;
val () = new_theory "vfmTest2602";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2602") $ get_result_defs "vfmTestDefs2602";
val () = export_theory_no_docs ();
