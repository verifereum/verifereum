open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2916Theory;
val () = new_theory "vfmTest2916";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2916") $ get_result_defs "vfmTestDefs2916";
val () = export_theory_no_docs ();
