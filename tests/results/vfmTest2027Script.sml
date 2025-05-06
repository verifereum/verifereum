open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2027Theory;
val () = new_theory "vfmTest2027";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2027") $ get_result_defs "vfmTestDefs2027";
val () = export_theory_no_docs ();
