open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2837Theory;
val () = new_theory "vfmTest2837";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2837") $ get_result_defs "vfmTestDefs2837";
val () = export_theory_no_docs ();
