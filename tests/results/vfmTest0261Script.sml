open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0261Theory;
val () = new_theory "vfmTest0261";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0261") $ get_result_defs "vfmTestDefs0261";
val () = export_theory_no_docs ();
