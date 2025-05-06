open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2703Theory;
val () = new_theory "vfmTest2703";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2703") $ get_result_defs "vfmTestDefs2703";
val () = export_theory_no_docs ();
