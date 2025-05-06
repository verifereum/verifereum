open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2533Theory;
val () = new_theory "vfmTest2533";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2533") $ get_result_defs "vfmTestDefs2533";
val () = export_theory_no_docs ();
