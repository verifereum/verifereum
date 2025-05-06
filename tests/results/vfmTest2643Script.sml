open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2643Theory;
val () = new_theory "vfmTest2643";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2643") $ get_result_defs "vfmTestDefs2643";
val () = export_theory_no_docs ();
