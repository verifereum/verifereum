open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2707Theory;
val () = new_theory "vfmTest2707";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2707") $ get_result_defs "vfmTestDefs2707";
val () = export_theory_no_docs ();
