open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2142Theory;
val () = new_theory "vfmTest2142";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2142") $ get_result_defs "vfmTestDefs2142";
val () = export_theory_no_docs ();
