open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1070Theory;
val () = new_theory "vfmTest1070";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1070") $ get_result_defs "vfmTestDefs1070";
val () = export_theory_no_docs ();
