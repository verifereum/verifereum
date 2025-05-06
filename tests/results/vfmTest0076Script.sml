open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0076Theory;
val () = new_theory "vfmTest0076";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0076") $ get_result_defs "vfmTestDefs0076";
val () = export_theory_no_docs ();
