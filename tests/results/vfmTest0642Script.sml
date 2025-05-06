open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0642Theory;
val () = new_theory "vfmTest0642";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0642") $ get_result_defs "vfmTestDefs0642";
val () = export_theory_no_docs ();
