open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2912Theory;
val () = new_theory "vfmTest2912";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2912") $ get_result_defs "vfmTestDefs2912";
val () = export_theory_no_docs ();
