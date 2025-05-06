open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2477Theory;
val () = new_theory "vfmTest2477";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2477") $ get_result_defs "vfmTestDefs2477";
val () = export_theory_no_docs ();
