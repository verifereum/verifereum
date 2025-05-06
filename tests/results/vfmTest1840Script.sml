open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1840Theory;
val () = new_theory "vfmTest1840";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1840") $ get_result_defs "vfmTestDefs1840";
val () = export_theory_no_docs ();
