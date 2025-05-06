open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0679Theory;
val () = new_theory "vfmTest0679";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0679") $ get_result_defs "vfmTestDefs0679";
val () = export_theory_no_docs ();
