Theory vfmTest2330[no_sig_docs]
Ancestors vfmTestDefs2330
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2330_0.nsv", "result2330_1.nsv", "result2330_2.nsv", "result2330_3.nsv", "result2330_4.nsv", "result2330_5.nsv", "result2330_6.nsv", "result2330_7.nsv", "result2330_8.nsv", "result2330_9.nsv", "result2330_10.nsv", "result2330_11.nsv", "result2330_12.nsv", "result2330_13.nsv", "result2330_14.nsv", "result2330_15.nsv", "result2330_16.nsv", "result2330_17.nsv", "result2330_18.nsv", "result2330_19.nsv"];
val thyn = "vfmTestDefs2330";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
