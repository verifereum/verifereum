open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0868Theory;
val () = new_theory "vfmTest0868";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0868") $ get_result_defs "vfmTestDefs0868";
val () = export_theory_no_docs ();
