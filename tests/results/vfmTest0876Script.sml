open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0876Theory;
val () = new_theory "vfmTest0876";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0876") $ get_result_defs "vfmTestDefs0876";
val () = export_theory_no_docs ();
