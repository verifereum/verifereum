open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1793Theory;
val () = new_theory "vfmTest1793";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1793") $ get_result_defs "vfmTestDefs1793";
val () = export_theory_no_docs ();
