open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0215Theory;
val () = new_theory "vfmTest0215";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0215") $ get_result_defs "vfmTestDefs0215";
val () = export_theory_no_docs ();
