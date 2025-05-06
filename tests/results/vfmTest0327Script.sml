open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0327Theory;
val () = new_theory "vfmTest0327";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0327") $ get_result_defs "vfmTestDefs0327";
val () = export_theory_no_docs ();
