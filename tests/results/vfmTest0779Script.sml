open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0779Theory;
val () = new_theory "vfmTest0779";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0779") $ get_result_defs "vfmTestDefs0779";
val () = export_theory_no_docs ();
