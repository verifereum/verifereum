open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0187Theory;
val () = new_theory "vfmTest0187";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0187") $ get_result_defs "vfmTestDefs0187";
val () = export_theory_no_docs ();
