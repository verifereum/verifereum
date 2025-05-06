open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0606Theory;
val () = new_theory "vfmTest0606";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0606") $ get_result_defs "vfmTestDefs0606";
val () = export_theory_no_docs ();
