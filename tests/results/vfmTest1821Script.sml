open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1821Theory;
val () = new_theory "vfmTest1821";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1821") $ get_result_defs "vfmTestDefs1821";
val () = export_theory_no_docs ();
