open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2846Theory;
val () = new_theory "vfmTest2846";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2846") $ get_result_defs "vfmTestDefs2846";
val () = export_theory_no_docs ();
