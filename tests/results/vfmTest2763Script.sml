open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2763Theory;
val () = new_theory "vfmTest2763";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2763") $ get_result_defs "vfmTestDefs2763";
val () = export_theory_no_docs ();
