open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0030Theory;
val () = new_theory "vfmTest0030";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0030") $ get_result_defs "vfmTestDefs0030";
val () = export_theory_no_docs ();
