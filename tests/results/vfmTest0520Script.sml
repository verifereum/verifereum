open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0520Theory;
val () = new_theory "vfmTest0520";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0520") $ get_result_defs "vfmTestDefs0520";
val () = export_theory_no_docs ();
