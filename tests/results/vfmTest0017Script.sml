open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0017Theory;
val () = new_theory "vfmTest0017";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0017") $ get_result_defs "vfmTestDefs0017";
val () = export_theory_no_docs ();
