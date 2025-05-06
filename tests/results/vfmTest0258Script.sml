open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0258Theory;
val () = new_theory "vfmTest0258";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0258") $ get_result_defs "vfmTestDefs0258";
val () = export_theory_no_docs ();
