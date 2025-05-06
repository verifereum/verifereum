open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2754Theory;
val () = new_theory "vfmTest2754";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2754") $ get_result_defs "vfmTestDefs2754";
val () = export_theory_no_docs ();
