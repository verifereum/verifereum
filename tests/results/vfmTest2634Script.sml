open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2634Theory;
val () = new_theory "vfmTest2634";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2634") $ get_result_defs "vfmTestDefs2634";
val () = export_theory_no_docs ();
