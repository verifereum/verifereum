open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2467Theory;
val () = new_theory "vfmTest2467";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2467") $ get_result_defs "vfmTestDefs2467";
val () = export_theory_no_docs ();
