open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0867Theory;
val () = new_theory "vfmTest0867";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0867") $ get_result_defs "vfmTestDefs0867";
val () = export_theory_no_docs ();
