open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2208Theory;
val () = new_theory "vfmTest2208";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2208") $ get_result_defs "vfmTestDefs2208";
val () = export_theory_no_docs ();
