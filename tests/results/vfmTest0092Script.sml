open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0092Theory;
val () = new_theory "vfmTest0092";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0092") $ get_result_defs "vfmTestDefs0092";
val () = export_theory_no_docs ();
