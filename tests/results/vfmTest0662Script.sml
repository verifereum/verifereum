open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0662Theory;
val () = new_theory "vfmTest0662";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0662") $ get_result_defs "vfmTestDefs0662";
val () = export_theory_no_docs ();
