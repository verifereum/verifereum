Theory vfmTest2397[no_sig_docs]
Ancestors vfmTestDefs2397
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2397_0.nsv", "result2397_1.nsv", "result2397_2.nsv", "result2397_3.nsv", "result2397_4.nsv", "result2397_5.nsv", "result2397_6.nsv", "result2397_7.nsv", "result2397_8.nsv", "result2397_9.nsv", "result2397_10.nsv", "result2397_11.nsv", "result2397_12.nsv", "result2397_13.nsv", "result2397_14.nsv", "result2397_15.nsv", "result2397_16.nsv", "result2397_17.nsv", "result2397_18.nsv", "result2397_19.nsv"];
val thyn = "vfmTestDefs2397";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
