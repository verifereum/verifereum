open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0272Theory;
val () = new_theory "vfmTest0272";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0272") $ get_result_defs "vfmTestDefs0272";
val () = export_theory_no_docs ();
