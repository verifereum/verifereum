open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2632Theory;
val () = new_theory "vfmTest2632";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2632") $ get_result_defs "vfmTestDefs2632";
val () = export_theory_no_docs ();
