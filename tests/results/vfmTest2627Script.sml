open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2627Theory;
val () = new_theory "vfmTest2627";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2627") $ get_result_defs "vfmTestDefs2627";
val () = export_theory_no_docs ();
