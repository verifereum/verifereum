open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0631Theory;
val () = new_theory "vfmTest0631";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0631") $ get_result_defs "vfmTestDefs0631";
val () = export_theory_no_docs ();
