open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2900Theory;
val () = new_theory "vfmTest2900";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2900") $ get_result_defs "vfmTestDefs2900";
val () = export_theory_no_docs ();
