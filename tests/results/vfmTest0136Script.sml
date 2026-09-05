Theory vfmTest0136[no_sig_docs]
Ancestors vfmTestDefs0136
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0136_0.nsv", "result0136_1.nsv", "result0136_2.nsv"];
val thyn = "vfmTestDefs0136";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
