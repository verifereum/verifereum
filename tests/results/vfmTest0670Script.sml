open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0670Theory;
val () = new_theory "vfmTest0670";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0670") $ get_result_defs "vfmTestDefs0670";
val () = export_theory_no_docs ();
