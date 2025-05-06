open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0717Theory;
val () = new_theory "vfmTest0717";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0717") $ get_result_defs "vfmTestDefs0717";
val () = export_theory_no_docs ();
