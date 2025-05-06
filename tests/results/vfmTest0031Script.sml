open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0031Theory;
val () = new_theory "vfmTest0031";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0031") $ get_result_defs "vfmTestDefs0031";
val () = export_theory_no_docs ();
