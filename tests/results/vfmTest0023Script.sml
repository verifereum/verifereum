open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0023Theory;
val () = new_theory "vfmTest0023";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0023") $ get_result_defs "vfmTestDefs0023";
val () = export_theory_no_docs ();
