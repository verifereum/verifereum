open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0842Theory;
val () = new_theory "vfmTest0842";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0842") $ get_result_defs "vfmTestDefs0842";
val () = export_theory_no_docs ();
