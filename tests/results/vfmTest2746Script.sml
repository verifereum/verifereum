open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2746Theory;
val () = new_theory "vfmTest2746";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2746") $ get_result_defs "vfmTestDefs2746";
val () = export_theory_no_docs ();
