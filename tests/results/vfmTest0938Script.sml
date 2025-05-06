open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0938Theory;
val () = new_theory "vfmTest0938";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0938") $ get_result_defs "vfmTestDefs0938";
val () = export_theory_no_docs ();
