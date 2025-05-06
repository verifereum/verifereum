open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2207Theory;
val () = new_theory "vfmTest2207";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2207") $ get_result_defs "vfmTestDefs2207";
val () = export_theory_no_docs ();
