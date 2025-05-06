open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0142Theory;
val () = new_theory "vfmTest0142";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0142") $ get_result_defs "vfmTestDefs0142";
val () = export_theory_no_docs ();
