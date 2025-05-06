open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0866Theory;
val () = new_theory "vfmTest0866";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0866") $ get_result_defs "vfmTestDefs0866";
val () = export_theory_no_docs ();
