open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0693Theory;
val () = new_theory "vfmTest0693";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0693") $ get_result_defs "vfmTestDefs0693";
val () = export_theory_no_docs ();
