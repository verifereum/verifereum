open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2716Theory;
val () = new_theory "vfmTest2716";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2716") $ get_result_defs "vfmTestDefs2716";
val () = export_theory_no_docs ();
