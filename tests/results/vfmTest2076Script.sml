open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2076Theory;
val () = new_theory "vfmTest2076";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2076") $ get_result_defs "vfmTestDefs2076";
val () = export_theory_no_docs ();
