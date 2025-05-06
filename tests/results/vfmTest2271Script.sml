open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2271Theory;
val () = new_theory "vfmTest2271";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2271") $ get_result_defs "vfmTestDefs2271";
val () = export_theory_no_docs ();
