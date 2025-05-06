open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0419Theory;
val () = new_theory "vfmTest0419";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0419") $ get_result_defs "vfmTestDefs0419";
val () = export_theory_no_docs ();
