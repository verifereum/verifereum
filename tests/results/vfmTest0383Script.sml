open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0383Theory;
val () = new_theory "vfmTest0383";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0383") $ get_result_defs "vfmTestDefs0383";
val () = export_theory_no_docs ();
