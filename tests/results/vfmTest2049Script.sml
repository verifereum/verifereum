open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2049Theory;
val () = new_theory "vfmTest2049";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2049") $ get_result_defs "vfmTestDefs2049";
val () = export_theory_no_docs ();
