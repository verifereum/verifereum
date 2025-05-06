open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0447Theory;
val () = new_theory "vfmTest0447";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0447") $ get_result_defs "vfmTestDefs0447";
val () = export_theory_no_docs ();
