open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0073Theory;
val () = new_theory "vfmTest0073";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0073") $ get_result_defs "vfmTestDefs0073";
val () = export_theory_no_docs ();
