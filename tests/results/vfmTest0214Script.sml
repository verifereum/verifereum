open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0214Theory;
val () = new_theory "vfmTest0214";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0214") $ get_result_defs "vfmTestDefs0214";
val () = export_theory_no_docs ();
