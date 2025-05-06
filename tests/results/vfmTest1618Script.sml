open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1618Theory;
val () = new_theory "vfmTest1618";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1618") $ get_result_defs "vfmTestDefs1618";
val () = export_theory_no_docs ();
