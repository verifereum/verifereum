open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0070Theory;
val () = new_theory "vfmTest0070";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0070") $ get_result_defs "vfmTestDefs0070";
val () = export_theory_no_docs ();
