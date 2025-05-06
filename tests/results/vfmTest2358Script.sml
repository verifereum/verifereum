open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2358Theory;
val () = new_theory "vfmTest2358";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2358") $ get_result_defs "vfmTestDefs2358";
val () = export_theory_no_docs ();
