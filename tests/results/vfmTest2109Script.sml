Theory vfmTest2109[no_sig_docs]
Ancestors vfmTestDefs2109
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2109_0.nsv", "result2109_1.nsv", "result2109_2.nsv", "result2109_3.nsv", "result2109_4.nsv", "result2109_5.nsv", "result2109_6.nsv", "result2109_7.nsv", "result2109_8.nsv", "result2109_9.nsv", "result2109_10.nsv", "result2109_11.nsv", "result2109_12.nsv", "result2109_13.nsv", "result2109_14.nsv", "result2109_15.nsv", "result2109_16.nsv", "result2109_17.nsv"];
val thyn = "vfmTestDefs2109";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
