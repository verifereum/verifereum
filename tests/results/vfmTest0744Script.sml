open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0744Theory;
val () = new_theory "vfmTest0744";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0744") $ get_result_defs "vfmTestDefs0744";
val () = export_theory_no_docs ();
