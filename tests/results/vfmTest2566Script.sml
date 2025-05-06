open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2566Theory;
val () = new_theory "vfmTest2566";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2566") $ get_result_defs "vfmTestDefs2566";
val () = export_theory_no_docs ();
