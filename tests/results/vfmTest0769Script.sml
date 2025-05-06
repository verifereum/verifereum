open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0769Theory;
val () = new_theory "vfmTest0769";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0769") $ get_result_defs "vfmTestDefs0769";
val () = export_theory_no_docs ();
