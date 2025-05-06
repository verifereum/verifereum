open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0995Theory;
val () = new_theory "vfmTest0995";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0995") $ get_result_defs "vfmTestDefs0995";
val () = export_theory_no_docs ();
