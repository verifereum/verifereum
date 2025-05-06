open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2743Theory;
val () = new_theory "vfmTest2743";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2743") $ get_result_defs "vfmTestDefs2743";
val () = export_theory_no_docs ();
