open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0997Theory;
val () = new_theory "vfmTest0997";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0997") $ get_result_defs "vfmTestDefs0997";
val () = export_theory_no_docs ();
