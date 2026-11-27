Theory vfmTest2162[no_sig_docs]
Ancestors vfmTestDefs2162
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2162_0.nsv", "result2162_1.nsv", "result2162_2.nsv", "result2162_3.nsv", "result2162_4.nsv", "result2162_5.nsv", "result2162_6.nsv", "result2162_7.nsv", "result2162_8.nsv", "result2162_9.nsv", "result2162_10.nsv", "result2162_11.nsv", "result2162_12.nsv", "result2162_13.nsv", "result2162_14.nsv", "result2162_15.nsv", "result2162_16.nsv", "result2162_17.nsv", "result2162_18.nsv", "result2162_19.nsv", "result2162_20.nsv", "result2162_21.nsv", "result2162_22.nsv", "result2162_23.nsv", "result2162_24.nsv", "result2162_25.nsv", "result2162_26.nsv"];
val thyn = "vfmTestDefs2162";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
