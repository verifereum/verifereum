open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0943Theory;
val () = new_theory "vfmTest0943";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0943") $ get_result_defs "vfmTestDefs0943";
val () = export_theory_no_docs ();
