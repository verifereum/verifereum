open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2387Theory;
val () = new_theory "vfmTest2387";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2387") $ get_result_defs "vfmTestDefs2387";
val () = export_theory_no_docs ();
