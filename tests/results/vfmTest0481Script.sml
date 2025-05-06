open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0481Theory;
val () = new_theory "vfmTest0481";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0481") $ get_result_defs "vfmTestDefs0481";
val () = export_theory_no_docs ();
