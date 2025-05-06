open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0990Theory;
val () = new_theory "vfmTest0990";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0990") $ get_result_defs "vfmTestDefs0990";
val () = export_theory_no_docs ();
