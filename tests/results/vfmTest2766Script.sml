open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2766Theory;
val () = new_theory "vfmTest2766";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2766") $ get_result_defs "vfmTestDefs2766";
val () = export_theory_no_docs ();
