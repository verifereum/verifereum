open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2210Theory;
val () = new_theory "vfmTest2210";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2210") $ get_result_defs "vfmTestDefs2210";
val () = export_theory_no_docs ();
