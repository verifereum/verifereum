open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0179Theory;
val () = new_theory "vfmTest0179";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0179") $ get_result_defs "vfmTestDefs0179";
val () = export_theory_no_docs ();
