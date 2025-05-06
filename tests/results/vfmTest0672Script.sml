open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0672Theory;
val () = new_theory "vfmTest0672";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0672") $ get_result_defs "vfmTestDefs0672";
val () = export_theory_no_docs ();
