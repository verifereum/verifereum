open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2483Theory;
val () = new_theory "vfmTest2483";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2483") $ get_result_defs "vfmTestDefs2483";
val () = export_theory_no_docs ();
