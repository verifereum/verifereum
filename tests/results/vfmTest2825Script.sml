open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2825Theory;
val () = new_theory "vfmTest2825";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2825") $ get_result_defs "vfmTestDefs2825";
val () = export_theory_no_docs ();
