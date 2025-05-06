open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1502Theory;
val () = new_theory "vfmTest1502";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1502") $ get_result_defs "vfmTestDefs1502";
val () = export_theory_no_docs ();
