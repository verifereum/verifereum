open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0135Theory;
val () = new_theory "vfmTest0135";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0135") $ get_result_defs "vfmTestDefs0135";
val () = export_theory_no_docs ();
