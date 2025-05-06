open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2053Theory;
val () = new_theory "vfmTest2053";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2053") $ get_result_defs "vfmTestDefs2053";
val () = export_theory_no_docs ();
