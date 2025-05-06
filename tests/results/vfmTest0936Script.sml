open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0936Theory;
val () = new_theory "vfmTest0936";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0936") $ get_result_defs "vfmTestDefs0936";
val () = export_theory_no_docs ();
