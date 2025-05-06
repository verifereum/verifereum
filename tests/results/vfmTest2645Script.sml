open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2645Theory;
val () = new_theory "vfmTest2645";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2645") $ get_result_defs "vfmTestDefs2645";
val () = export_theory_no_docs ();
