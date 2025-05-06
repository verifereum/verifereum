open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2739Theory;
val () = new_theory "vfmTest2739";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2739") $ get_result_defs "vfmTestDefs2739";
val () = export_theory_no_docs ();
