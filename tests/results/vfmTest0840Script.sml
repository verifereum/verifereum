open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0840Theory;
val () = new_theory "vfmTest0840";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0840") $ get_result_defs "vfmTestDefs0840";
val () = export_theory_no_docs ();
