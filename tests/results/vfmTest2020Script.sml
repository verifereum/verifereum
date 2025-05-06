open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2020Theory;
val () = new_theory "vfmTest2020";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2020") $ get_result_defs "vfmTestDefs2020";
val () = export_theory_no_docs ();
