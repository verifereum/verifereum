open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0163Theory;
val () = new_theory "vfmTest0163";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0163") $ get_result_defs "vfmTestDefs0163";
val () = export_theory_no_docs ();
