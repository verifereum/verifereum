open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0983Theory;
val () = new_theory "vfmTest0983";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0983") $ get_result_defs "vfmTestDefs0983";
val () = export_theory_no_docs ();
