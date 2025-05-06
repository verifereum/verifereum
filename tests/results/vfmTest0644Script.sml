open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0644Theory;
val () = new_theory "vfmTest0644";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0644") $ get_result_defs "vfmTestDefs0644";
val () = export_theory_no_docs ();
