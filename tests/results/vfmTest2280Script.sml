open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2280Theory;
val () = new_theory "vfmTest2280";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2280") $ get_result_defs "vfmTestDefs2280";
val () = export_theory_no_docs ();
