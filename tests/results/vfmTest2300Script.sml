open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2300Theory;
val () = new_theory "vfmTest2300";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2300") $ get_result_defs "vfmTestDefs2300";
val () = export_theory_no_docs ();
