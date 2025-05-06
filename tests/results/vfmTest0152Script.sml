open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0152Theory;
val () = new_theory "vfmTest0152";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0152") $ get_result_defs "vfmTestDefs0152";
val () = export_theory_no_docs ();
