open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0721Theory;
val () = new_theory "vfmTest0721";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0721") $ get_result_defs "vfmTestDefs0721";
val () = export_theory_no_docs ();
