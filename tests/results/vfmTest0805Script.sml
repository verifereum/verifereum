open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0805Theory;
val () = new_theory "vfmTest0805";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0805") $ get_result_defs "vfmTestDefs0805";
val () = export_theory_no_docs ();
