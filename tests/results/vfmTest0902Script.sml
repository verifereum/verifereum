open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0902Theory;
val () = new_theory "vfmTest0902";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0902") $ get_result_defs "vfmTestDefs0902";
val () = export_theory_no_docs ();
