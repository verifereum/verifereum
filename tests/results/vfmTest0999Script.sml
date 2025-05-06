open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0999Theory;
val () = new_theory "vfmTest0999";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0999") $ get_result_defs "vfmTestDefs0999";
val () = export_theory_no_docs ();
