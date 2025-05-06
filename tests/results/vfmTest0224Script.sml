open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0224Theory;
val () = new_theory "vfmTest0224";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0224") $ get_result_defs "vfmTestDefs0224";
val () = export_theory_no_docs ();
