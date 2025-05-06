open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0446Theory;
val () = new_theory "vfmTest0446";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0446") $ get_result_defs "vfmTestDefs0446";
val () = export_theory_no_docs ();
