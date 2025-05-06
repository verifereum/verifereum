open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0618Theory;
val () = new_theory "vfmTest0618";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0618") $ get_result_defs "vfmTestDefs0618";
val () = export_theory_no_docs ();
