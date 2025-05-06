open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2043Theory;
val () = new_theory "vfmTest2043";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2043") $ get_result_defs "vfmTestDefs2043";
val () = export_theory_no_docs ();
