open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1114Theory;
val () = new_theory "vfmTest1114";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1114") $ get_result_defs "vfmTestDefs1114";
val () = export_theory_no_docs ();
