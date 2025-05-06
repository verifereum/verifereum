open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1670Theory;
val () = new_theory "vfmTest1670";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1670") $ get_result_defs "vfmTestDefs1670";
val () = export_theory_no_docs ();
