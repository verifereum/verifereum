open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0600Theory;
val () = new_theory "vfmTest0600";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0600") $ get_result_defs "vfmTestDefs0600";
val () = export_theory_no_docs ();
