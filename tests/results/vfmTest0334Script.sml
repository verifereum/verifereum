open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0334Theory;
val () = new_theory "vfmTest0334";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0334") $ get_result_defs "vfmTestDefs0334";
val () = export_theory_no_docs ();
