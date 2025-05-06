open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0858Theory;
val () = new_theory "vfmTest0858";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0858") $ get_result_defs "vfmTestDefs0858";
val () = export_theory_no_docs ();
