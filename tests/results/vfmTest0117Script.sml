open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0117Theory;
val () = new_theory "vfmTest0117";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0117") $ get_result_defs "vfmTestDefs0117";
val () = export_theory_no_docs ();
