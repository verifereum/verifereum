open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0283Theory;
val () = new_theory "vfmTest0283";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0283") $ get_result_defs "vfmTestDefs0283";
val () = export_theory_no_docs ();
