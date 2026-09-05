Theory vfmTest0225[no_sig_docs]
Ancestors vfmTestDefs0225
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0225_0.nsv", "result0225_1.nsv", "result0225_2.nsv", "result0225_3.nsv"];
val thyn = "vfmTestDefs0225";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
