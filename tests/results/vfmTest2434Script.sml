open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2434Theory;
val () = new_theory "vfmTest2434";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2434") $ get_result_defs "vfmTestDefs2434";
val () = export_theory_no_docs ();
