open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2030Theory;
val () = new_theory "vfmTest2030";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2030") $ get_result_defs "vfmTestDefs2030";
val () = export_theory_no_docs ();
