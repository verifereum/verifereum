open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0716Theory;
val () = new_theory "vfmTest0716";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0716") $ get_result_defs "vfmTestDefs0716";
val () = export_theory_no_docs ();
