open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2405Theory;
val () = new_theory "vfmTest2405";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2405") $ get_result_defs "vfmTestDefs2405";
val () = export_theory_no_docs ();
