open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0059Theory;
val () = new_theory "vfmTest0059";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0059") $ get_result_defs "vfmTestDefs0059";
val () = export_theory_no_docs ();
