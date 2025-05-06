open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0640Theory;
val () = new_theory "vfmTest0640";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0640") $ get_result_defs "vfmTestDefs0640";
val () = export_theory_no_docs ();
