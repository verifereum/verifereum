open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0474Theory;
val () = new_theory "vfmTest0474";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0474") $ get_result_defs "vfmTestDefs0474";
val () = export_theory_no_docs ();
