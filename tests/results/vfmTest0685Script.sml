open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0685Theory;
val () = new_theory "vfmTest0685";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0685") $ get_result_defs "vfmTestDefs0685";
val () = export_theory_no_docs ();
