open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2040Theory;
val () = new_theory "vfmTest2040";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2040") $ get_result_defs "vfmTestDefs2040";
val () = export_theory_no_docs ();
