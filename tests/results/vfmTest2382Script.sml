Theory vfmTest2382[no_sig_docs]
Ancestors vfmTestDefs2382
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2382_0.nsv", "result2382_1.nsv", "result2382_2.nsv", "result2382_3.nsv", "result2382_4.nsv", "result2382_5.nsv", "result2382_6.nsv", "result2382_7.nsv", "result2382_8.nsv", "result2382_9.nsv", "result2382_10.nsv", "result2382_11.nsv", "result2382_12.nsv", "result2382_13.nsv", "result2382_14.nsv", "result2382_15.nsv", "result2382_16.nsv", "result2382_17.nsv", "result2382_18.nsv", "result2382_19.nsv"];
val thyn = "vfmTestDefs2382";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
