open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0312Theory;
val () = new_theory "vfmTest0312";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0312") $ get_result_defs "vfmTestDefs0312";
val () = export_theory_no_docs ();
