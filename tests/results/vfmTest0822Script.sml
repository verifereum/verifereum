open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0822Theory;
val () = new_theory "vfmTest0822";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0822") $ get_result_defs "vfmTestDefs0822";
val () = export_theory_no_docs ();
