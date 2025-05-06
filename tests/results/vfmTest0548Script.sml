open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0548Theory;
val () = new_theory "vfmTest0548";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0548") $ get_result_defs "vfmTestDefs0548";
val () = export_theory_no_docs ();
