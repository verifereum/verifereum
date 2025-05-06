open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0707Theory;
val () = new_theory "vfmTest0707";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0707") $ get_result_defs "vfmTestDefs0707";
val () = export_theory_no_docs ();
