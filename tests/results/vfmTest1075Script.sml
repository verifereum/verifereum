Theory vfmTest1075[no_sig_docs]
Ancestors vfmTestDefs1075
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1075_0.nsv", "result1075_1.nsv", "result1075_2.nsv", "result1075_3.nsv", "result1075_4.nsv", "result1075_5.nsv", "result1075_6.nsv", "result1075_7.nsv", "result1075_8.nsv", "result1075_9.nsv"];
val thyn = "vfmTestDefs1075";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
