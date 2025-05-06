open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2720Theory;
val () = new_theory "vfmTest2720";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2720") $ get_result_defs "vfmTestDefs2720";
val () = export_theory_no_docs ();
