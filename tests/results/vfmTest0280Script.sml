open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0280Theory;
val () = new_theory "vfmTest0280";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0280") $ get_result_defs "vfmTestDefs0280";
val () = export_theory_no_docs ();
