open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1660Theory;
val () = new_theory "vfmTest1660";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1660") $ get_result_defs "vfmTestDefs1660";
val () = export_theory_no_docs ();
