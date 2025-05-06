open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1537Theory;
val () = new_theory "vfmTest1537";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1537") $ get_result_defs "vfmTestDefs1537";
val () = export_theory_no_docs ();
