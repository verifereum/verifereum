open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0549Theory;
val () = new_theory "vfmTest0549";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0549") $ get_result_defs "vfmTestDefs0549";
val () = export_theory_no_docs ();
