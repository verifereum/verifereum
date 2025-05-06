open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2925Theory;
val () = new_theory "vfmTest2925";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2925") $ get_result_defs "vfmTestDefs2925";
val () = export_theory_no_docs ();
