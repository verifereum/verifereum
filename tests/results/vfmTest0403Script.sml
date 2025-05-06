open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0403Theory;
val () = new_theory "vfmTest0403";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0403") $ get_result_defs "vfmTestDefs0403";
val () = export_theory_no_docs ();
