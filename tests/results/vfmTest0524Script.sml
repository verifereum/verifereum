open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0524Theory;
val () = new_theory "vfmTest0524";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0524") $ get_result_defs "vfmTestDefs0524";
val () = export_theory_no_docs ();
