open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2845Theory;
val () = new_theory "vfmTest2845";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2845") $ get_result_defs "vfmTestDefs2845";
val () = export_theory_no_docs ();
