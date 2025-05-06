open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0969Theory;
val () = new_theory "vfmTest0969";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0969") $ get_result_defs "vfmTestDefs0969";
val () = export_theory_no_docs ();
