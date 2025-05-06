open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2588Theory;
val () = new_theory "vfmTest2588";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2588") $ get_result_defs "vfmTestDefs2588";
val () = export_theory_no_docs ();
