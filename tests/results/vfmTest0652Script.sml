open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0652Theory;
val () = new_theory "vfmTest0652";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0652") $ get_result_defs "vfmTestDefs0652";
val () = export_theory_no_docs ();
