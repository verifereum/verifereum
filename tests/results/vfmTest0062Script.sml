open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0062Theory;
val () = new_theory "vfmTest0062";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0062") $ get_result_defs "vfmTestDefs0062";
val () = export_theory_no_docs ();
