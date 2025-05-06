open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0408Theory;
val () = new_theory "vfmTest0408";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0408") $ get_result_defs "vfmTestDefs0408";
val () = export_theory_no_docs ();
