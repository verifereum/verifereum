open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2882Theory;
val () = new_theory "vfmTest2882";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2882") $ get_result_defs "vfmTestDefs2882";
val () = export_theory_no_docs ();
