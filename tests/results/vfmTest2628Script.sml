open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2628Theory;
val () = new_theory "vfmTest2628";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2628") $ get_result_defs "vfmTestDefs2628";
val () = export_theory_no_docs ();
