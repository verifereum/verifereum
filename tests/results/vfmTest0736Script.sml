open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0736Theory;
val () = new_theory "vfmTest0736";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0736") $ get_result_defs "vfmTestDefs0736";
val () = export_theory_no_docs ();
