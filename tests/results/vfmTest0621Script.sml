open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0621Theory;
val () = new_theory "vfmTest0621";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0621") $ get_result_defs "vfmTestDefs0621";
val () = export_theory_no_docs ();
