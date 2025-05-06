open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2011Theory;
val () = new_theory "vfmTest2011";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2011") $ get_result_defs "vfmTestDefs2011";
val () = export_theory_no_docs ();
