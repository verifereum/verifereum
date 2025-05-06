open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2535Theory;
val () = new_theory "vfmTest2535";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2535") $ get_result_defs "vfmTestDefs2535";
val () = export_theory_no_docs ();
