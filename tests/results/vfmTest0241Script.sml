Theory vfmTest0241[no_sig_docs]
Ancestors vfmTestDefs0241
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0241_0.nsv", "result0241_1.nsv", "result0241_2.nsv", "result0241_3.nsv"];
val thyn = "vfmTestDefs0241";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
