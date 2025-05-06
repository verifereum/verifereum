open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2735Theory;
val () = new_theory "vfmTest2735";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2735") $ get_result_defs "vfmTestDefs2735";
val () = export_theory_no_docs ();
