Theory vfmTest2308[no_sig_docs]
Ancestors vfmTestDefs2308
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2308_0.nsv", "result2308_1.nsv", "result2308_2.nsv", "result2308_3.nsv", "result2308_4.nsv", "result2308_5.nsv", "result2308_6.nsv", "result2308_7.nsv", "result2308_8.nsv", "result2308_9.nsv", "result2308_10.nsv", "result2308_11.nsv", "result2308_12.nsv", "result2308_13.nsv", "result2308_14.nsv", "result2308_15.nsv", "result2308_16.nsv", "result2308_17.nsv", "result2308_18.nsv", "result2308_19.nsv"];
val thyn = "vfmTestDefs2308";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
