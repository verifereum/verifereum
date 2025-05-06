open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0802Theory;
val () = new_theory "vfmTest0802";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0802") $ get_result_defs "vfmTestDefs0802";
val () = export_theory_no_docs ();
